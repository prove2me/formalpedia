-- Prove2me | solution 1 for jacobiTheta_two_eq_tprod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e6c37b3c-400a-5bec-a116-434c5e849d0b

import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_jacobiTheta_two_eq_tprod

set_option autoImplicit false

noncomputable section

namespace JTPEngine

open Finset

def qfact (Q : ℂ) (m : ℕ) : ℂ := ∏ i ∈ Finset.range m, (1 - Q ^ (i + 1))

def qbinom (Q : ℂ) (m k : ℕ) : ℂ :=
  if k ≤ m then qfact Q m / (qfact Q k * qfact Q (m - k)) else 0

@[scoped simp] theorem qfact_zero (Q : ℂ) : qfact Q 0 = 1 := by
  unfold qfact
  exact Finset.prod_range_zero _

theorem qfact_succ (Q : ℂ) (m : ℕ) : qfact Q (m + 1) = qfact Q m * (1 - Q ^ (m + 1)) := by
  unfold qfact
  exact Finset.prod_range_succ _ m

theorem one_sub_pow_ne_zero {Q : ℂ} (hQ : ‖Q‖ < 1) (i : ℕ) : 1 - Q ^ (i + 1) ≠ 0 := by
  intro h
  have h1 : Q ^ (i + 1) = 1 := by
    have := sub_eq_zero.mp h
    exact this.symm
  have h2 : ‖Q ^ (i + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hQ (Nat.succ_ne_zero i)
  rw [h1, norm_one] at h2
  exact lt_irrefl 1 h2

theorem qfact_ne_zero {Q : ℂ} (hQ : ‖Q‖ < 1) (m : ℕ) : qfact Q m ≠ 0 := by
  unfold qfact
  rw [Finset.prod_ne_zero_iff]
  exact fun i _ => one_sub_pow_ne_zero hQ i

theorem qbinom_zero_right {Q : ℂ} (hQ : ‖Q‖ < 1) (m : ℕ) : qbinom Q m 0 = 1 := by
  unfold qbinom
  rw [if_pos (Nat.zero_le m), qfact_zero, one_mul, Nat.sub_zero,
    div_self (qfact_ne_zero hQ m)]

theorem qbinom_self {Q : ℂ} (hQ : ‖Q‖ < 1) (m : ℕ) : qbinom Q m m = 1 := by
  unfold qbinom
  rw [if_pos le_rfl, Nat.sub_self, qfact_zero, mul_one, div_self (qfact_ne_zero hQ m)]

theorem qbinom_of_gt (Q : ℂ) {m k : ℕ} (h : m < k) : qbinom Q m k = 0 := by
  unfold qbinom
  rw [if_neg (not_le.mpr h)]

theorem qbinom_succ_succ {Q : ℂ} (hQ : ‖Q‖ < 1) (m k : ℕ) :
    qbinom Q (m + 1) (k + 1) = qbinom Q m (k + 1) + Q ^ (m - k) * qbinom Q m k := by
  rcases lt_trichotomy k m with hkm | rfl | hkm
  ·
    have hk1m : k + 1 ≤ m := hkm
    unfold qbinom
    rw [if_pos (by omega : k + 1 ≤ m + 1), if_pos hk1m, if_pos (by omega : k ≤ m)]
    have e1 : m + 1 - (k + 1) = m - k := by omega
    have e2 : m - k = (m - (k + 1)) + 1 := by omega
    rw [e1, qfact_succ Q m, e2, qfact_succ Q (m - (k + 1))]
    have hf1 : qfact Q (k + 1) ≠ 0 := qfact_ne_zero hQ _
    have hf2 : qfact Q (m - (k + 1)) ≠ 0 := qfact_ne_zero hQ _
    have hf3 : qfact Q k ≠ 0 := qfact_ne_zero hQ _
    have hone : (1 : ℂ) - Q ^ (m - (k + 1) + 1) ≠ 0 := one_sub_pow_ne_zero hQ _
    rw [qfact_succ Q k]
    have hone2 : (1 : ℂ) - Q ^ (k + 1) ≠ 0 := one_sub_pow_ne_zero hQ _
    field_simp
    ring_nf
    have hpow : Q ^ 2 * Q ^ k * Q ^ (m - (1 + k)) = Q * Q ^ m := by
      calc Q ^ 2 * Q ^ k * Q ^ (m - (1 + k)) = Q ^ (2 + k + (m - (1 + k))) := by
            rw [← pow_add, ← pow_add]
        _ = Q ^ (1 + m) := by
            congr 1
            omega
        _ = Q * Q ^ m := by
            rw [pow_add, pow_one]
    linear_combination qfact Q m * hpow
  ·
    rw [qbinom_self hQ, qbinom_of_gt Q (Nat.lt_succ_self k), qbinom_self hQ,
      Nat.sub_self, pow_zero, zero_add, one_mul]
  ·
    rw [qbinom_of_gt Q (by omega : m < k + 1), qbinom_of_gt Q (by omega : m + 1 < k + 1),
      qbinom_of_gt Q hkm, mul_zero, add_zero]

theorem gauss_q {Q : ℂ} (hQ : ‖Q‖ < 1) (t : ℂ) (m : ℕ) :
    ∏ j ∈ Finset.range m, (1 + t * Q ^ j)
      = ∑ k ∈ Finset.range (m + 1), qbinom Q m k * Q ^ (k * (k - 1) / 2) * t ^ k := by
  induction m with
  | zero =>
    rw [Finset.prod_range_zero, Finset.sum_range_one, qbinom_zero_right hQ]
    norm_num
  | succ m ih =>
    have epow : ∀ k : ℕ, (k + 1) * ((k + 1) - 1) / 2 = k * (k - 1) / 2 + k := by
      intro k
      have h : (k + 1) * ((k + 1) - 1) = k * (k - 1) + 2 * k := by
        rcases k with _ | k'
        · norm_num
        · simp only [Nat.add_sub_cancel]
          ring
      rw [h, Nat.add_mul_div_left _ _ (by norm_num : (0 : ℕ) < 2)]
    rw [Finset.prod_range_succ, ih, mul_add, mul_one, Finset.sum_mul]

    rw [Finset.sum_range_succ' (fun k => qbinom Q (m + 1) k * Q ^ (k * (k - 1) / 2) * t ^ k) (m + 1)]

    have hterm : ∀ k ∈ Finset.range (m + 1),
        qbinom Q (m + 1) (k + 1) * Q ^ ((k + 1) * ((k + 1) - 1) / 2) * t ^ (k + 1)
          = qbinom Q m (k + 1) * Q ^ ((k + 1) * ((k + 1) - 1) / 2) * t ^ (k + 1)
            + qbinom Q m k * Q ^ (k * (k - 1) / 2) * t ^ k * (t * Q ^ m) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hkm : k ≤ m := by omega
      rw [qbinom_succ_succ hQ, add_mul, add_mul]
      congr 1

      rw [epow k]
      have hexp : Q ^ (m - k) * Q ^ (k * (k - 1) / 2 + k) = Q ^ (k * (k - 1) / 2) * Q ^ m := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      calc Q ^ (m - k) * qbinom Q m k * Q ^ (k * (k - 1) / 2 + k) * t ^ (k + 1)
          = qbinom Q m k * (Q ^ (m - k) * Q ^ (k * (k - 1) / 2 + k)) * t ^ (k + 1) := by ring
        _ = qbinom Q m k * (Q ^ (k * (k - 1) / 2) * Q ^ m) * t ^ (k + 1) := by rw [hexp]
        _ = qbinom Q m k * Q ^ (k * (k - 1) / 2) * t ^ k * (t * Q ^ m) := by
            rw [pow_succ]
            ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]

    have h1 : (qbinom Q (m + 1) 0 * Q ^ (0 * (0 - 1) / 2) * t ^ 0 : ℂ) = 1 := by
      rw [qbinom_zero_right hQ]
      norm_num
    have hfold : ∑ k ∈ Finset.range (m + 1), qbinom Q m k * Q ^ (k * (k - 1) / 2) * t ^ k
        = (∑ k ∈ Finset.range (m + 1),
            qbinom Q m (k + 1) * Q ^ ((k + 1) * ((k + 1) - 1) / 2) * t ^ (k + 1)) + 1 := by
      have key := Finset.sum_range_succ'
        (fun k => qbinom Q m k * Q ^ (k * (k - 1) / 2) * t ^ k) (m + 1)
      rw [Finset.sum_range_succ, qbinom_of_gt Q (Nat.lt_succ_self m), zero_mul, zero_mul,
        add_zero] at key
      rw [key]
      congr 1
      rw [qbinom_zero_right hQ]
      norm_num
    rw [hfold, h1]
    ring

private theorem prod_zpow' {q : ℂ} (hq0 : q ≠ 0) (s : Finset ℕ) (f : ℕ → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← zpow_add₀ hq0]

private theorem two_dvd_mul_pred (k : ℕ) : 2 ∣ k * (k - 1) := by
  rcases k with _ | k'
  · norm_num
  · simp only [Nat.add_sub_cancel]
    rw [mul_comm]
    exact (Nat.even_mul_succ_self k').two_dvd

theorem finite_jtp {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {x : ℂ} (hx : x ≠ 0) (N : ℕ) :
    ∏ j ∈ Finset.range N, ((1 + x * q ^ (2 * j + 1)) * (1 + x⁻¹ * q ^ (2 * j + 1)))
      = ∑ k ∈ Finset.range (2 * N + 1),
          qbinom (q ^ 2) (2 * N) k * q ^ (((k : ℤ) - N) ^ 2) * x ^ ((k : ℤ) - N) := by
  have hQ2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have G := gauss_q hQ2 (x * q ^ ((1 : ℤ) - 2 * N)) (2 * N)

  have hfac : ∀ j : ℕ, 1 + x * q ^ ((1 : ℤ) - 2 * N) * (q ^ 2) ^ j
      = 1 + x * q ^ (2 * (j : ℤ) + 1 - 2 * N) := by
    intro j
    congr 1
    rw [show ((q : ℂ) ^ 2) ^ j = q ^ ((2 * j : ℕ)) by rw [← pow_mul],
      ← zpow_natCast q (2 * j), mul_assoc, ← zpow_add₀ hq0]
    congr 2
    push_cast
    ring
  rw [Finset.prod_congr rfl (fun j _ => hfac j),
    show Finset.range (2 * N) = Finset.range (N + N) from by rw [two_mul],
    Finset.prod_range_add] at G

  have hup : ∀ j : ℕ, 1 + x * q ^ (2 * ((N + j : ℕ) : ℤ) + 1 - 2 * N)
      = 1 + x * q ^ (2 * j + 1) := by
    intro j
    congr 1
    rw [show (2 * ((N + j : ℕ) : ℤ) + 1 - 2 * N) = ((2 * j + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]

  have hlow : ∀ j ∈ Finset.range N, 1 + x * q ^ (2 * (j : ℤ) + 1 - 2 * N)
      = (x * q ^ (2 * (j : ℤ) + 1 - 2 * N)) * (1 + x⁻¹ * q ^ ((2 * (N - 1 - j) + 1 : ℕ))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : j ≤ N - 1 := by omega
    have h2 : 1 ≤ N := by omega
    have hc : ((2 * (N - 1 - j) + 1 : ℕ) : ℤ) = -(2 * (j : ℤ) + 1 - 2 * N) := by
      push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
      ring
    have hcancel : x * q ^ (2 * (j : ℤ) + 1 - 2 * N)
        * (x⁻¹ * q ^ (-(2 * (j : ℤ) + 1 - 2 * N))) = 1 := by
      rw [mul_mul_mul_comm, mul_inv_cancel₀ hx, ← zpow_add₀ hq0, add_neg_cancel, zpow_zero,
        one_mul]
    rw [mul_add, mul_one, ← zpow_natCast q (2 * (N - 1 - j) + 1), hc, hcancel]
    ring
  rw [Finset.prod_congr rfl hlow, Finset.prod_congr rfl (fun j _ => hup j),
    Finset.prod_mul_distrib] at G

  have hodd : ∀ n : ℕ, ∑ j ∈ Finset.range n, (2 * (j : ℤ) + 1) = (n : ℤ) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hsum : ∑ j ∈ Finset.range N, (2 * (j : ℤ) + 1 - 2 * N) = -(N : ℤ) ^ 2 := by
    rw [Finset.sum_sub_distrib, hodd N, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hscal : ∏ j ∈ Finset.range N, (x * q ^ (2 * (j : ℤ) + 1 - 2 * N))
      = x ^ N * q ^ (-(N : ℤ) ^ 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, prod_zpow' hq0, hsum]
  rw [hscal] at G

  have hrefl : ∏ j ∈ Finset.range N, (1 + x⁻¹ * q ^ (2 * (N - 1 - j) + 1))
      = ∏ j ∈ Finset.range N, (1 + x⁻¹ * q ^ (2 * j + 1)) :=
    Finset.prod_range_reflect (fun j => 1 + x⁻¹ * q ^ (2 * j + 1)) N
  rw [hrefl] at G

  have hRterm : ∀ k ∈ Finset.range (2 * N + 1),
      qbinom (q ^ 2) (2 * N) k * (q ^ 2) ^ (k * (k - 1) / 2) * (x * q ^ ((1 : ℤ) - 2 * N)) ^ k
        = x ^ N * q ^ (-(N : ℤ) ^ 2)
          * (qbinom (q ^ 2) (2 * N) k * q ^ (((k : ℤ) - N) ^ 2) * x ^ ((k : ℤ) - N)) := by
    intro k _
    have he : ((q : ℂ) ^ 2) ^ (k * (k - 1) / 2) = q ^ ((k * (k - 1) : ℕ)) := by
      rw [← pow_mul, Nat.mul_div_cancel' (two_dvd_mul_pred k)]
    have hx' : (x * q ^ ((1 : ℤ) - 2 * N)) ^ k
        = x ^ k * q ^ (((1 : ℤ) - 2 * N) * k) := by
      rw [mul_pow, ← zpow_natCast (q ^ ((1 : ℤ) - 2 * N)) k, ← zpow_mul]
    have hxsplit : (x : ℂ) ^ k = x ^ ((k : ℤ) - N) * x ^ N := by
      rw [← zpow_natCast x k, ← zpow_natCast x N, ← zpow_add₀ hx]
      congr 1
      ring
    have hkk : ((k * (k - 1) : ℕ) : ℤ) = (k : ℤ) ^ 2 - k := by
      rcases k with _ | k'
      · norm_num
      · push_cast [Nat.add_sub_cancel]
        ring
    have hqcollect : (q : ℂ) ^ ((k * (k - 1) : ℕ) : ℤ) * q ^ (((1 : ℤ) - 2 * N) * k)
        = q ^ (((k : ℤ) - N) ^ 2) * q ^ (-(N : ℤ) ^ 2) := by
      rw [← zpow_add₀ hq0, ← zpow_add₀ hq0]
      congr 1
      rw [hkk]
      ring
    rw [he, ← zpow_natCast q (k * (k - 1)), hx', hxsplit]
    calc qbinom (q ^ 2) (2 * N) k * q ^ ((k * (k - 1) : ℕ) : ℤ)
          * (x ^ ((k : ℤ) - N) * x ^ N * q ^ (((1 : ℤ) - 2 * N) * k))
        = qbinom (q ^ 2) (2 * N) k * x ^ ((k : ℤ) - N) * x ^ N
            * (q ^ ((k * (k - 1) : ℕ) : ℤ) * q ^ (((1 : ℤ) - 2 * N) * k)) := by ring
      _ = qbinom (q ^ 2) (2 * N) k * x ^ ((k : ℤ) - N) * x ^ N
            * (q ^ (((k : ℤ) - N) ^ 2) * q ^ (-(N : ℤ) ^ 2)) := by rw [hqcollect]
      _ = x ^ N * q ^ (-(N : ℤ) ^ 2)
            * (qbinom (q ^ 2) (2 * N) k * q ^ (((k : ℤ) - N) ^ 2) * x ^ ((k : ℤ) - N)) := by
          ring
  rw [Finset.sum_congr rfl hRterm, ← Finset.mul_sum, mul_assoc] at G
  have hC : (x ^ N * q ^ (-(N : ℤ) ^ 2) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero N hx) (zpow_ne_zero _ hq0)
  have G2 := mul_left_cancel₀ hC G
  rw [Finset.prod_mul_distrib, ← G2]
  ring

end JTPEngine
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

section R2
open Filter Topology

namespace JTPTannery

open JTPEngine (qfact)

variable {Q : ℂ}

theorem norm_pow_succ_lt_one (hQ : ‖Q‖ < 1) (i : ℕ) : ‖Q ^ (i + 1)‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hQ (Nat.succ_ne_zero i)

theorem one_sub_pow_ne_zero (hQ : ‖Q‖ < 1) (i : ℕ) : (1 : ℂ) - Q ^ (i + 1) ≠ 0 := by
  intro h
  have h1 : Q ^ (i + 1) = 1 := (sub_eq_zero.mp h).symm
  have h2 := norm_pow_succ_lt_one hQ i
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

theorem qfact_ne_zero (hQ : ‖Q‖ < 1) (m : ℕ) : qfact Q m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => one_sub_pow_ne_zero hQ i

theorem summable_norm_neg_pow (hQ : ‖Q‖ < 1) : Summable fun n : ℕ => ‖-Q ^ (n + 1)‖ := by
  have h : ∀ n : ℕ, ‖-Q ^ (n + 1)‖ = ‖Q‖ ^ n * ‖Q‖ := fun n => by
    rw [norm_neg, norm_pow, pow_succ]
  simp only [h]
  exact (summable_geometric_of_lt_one (norm_nonneg _) hQ).mul_right _

theorem summable_pow_succ (hQ : ‖Q‖ < 1) : Summable fun n : ℕ => ‖Q‖ ^ (n + 1) := by
  simp only [pow_succ]
  exact (summable_geometric_of_lt_one (norm_nonneg _) hQ).mul_right _

theorem pow_succ_lt_one (hQ : ‖Q‖ < 1) (i : ℕ) : ‖Q‖ ^ (i + 1) < 1 :=
  pow_lt_one₀ (norm_nonneg _) hQ (Nat.succ_ne_zero i)

theorem multipliable_one_sub_pow (hQ : ‖Q‖ < 1) : Multipliable fun n : ℕ => 1 - Q ^ (n + 1) :=
  (multipliable_one_add_of_summable (summable_norm_neg_pow hQ)).congr
    fun _ => (sub_eq_add_neg _ _).symm

theorem tendsto_qfact (hQ : ‖Q‖ < 1) :
    Tendsto (fun m => qfact Q m) atTop (𝓝 (∏' n : ℕ, (1 - Q ^ (n + 1)))) :=
  (multipliable_one_sub_pow hQ).tendsto_prod_tprod_nat

theorem tprod_one_sub_pow_ne_zero (hQ : ‖Q‖ < 1) : (∏' n : ℕ, (1 - Q ^ (n + 1))) ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -Q ^ (n + 1))
    (fun i => by rw [← sub_eq_add_neg]; exact one_sub_pow_ne_zero hQ i) (summable_norm_neg_pow hQ)
  simpa only [← sub_eq_add_neg] using h

theorem summable_norm_neg_pow_real (hQ : ‖Q‖ < 1) : Summable fun n : ℕ => ‖-(‖Q‖ ^ (n + 1))‖ := by
  simpa only [norm_neg, norm_pow, norm_norm] using summable_pow_succ hQ

theorem multipliable_pfact (hQ : ‖Q‖ < 1) : Multipliable fun n : ℕ => (1 : ℝ) - ‖Q‖ ^ (n + 1) :=
  (multipliable_one_add_of_summable (summable_norm_neg_pow_real hQ)).congr
    fun _ => (sub_eq_add_neg _ _).symm

theorem tprod_pfact_pos (hQ : ‖Q‖ < 1) : 0 < ∏' n : ℕ, ((1 : ℝ) - ‖Q‖ ^ (n + 1)) := by
  have hne : (∏' n : ℕ, ((1 : ℝ) + -(‖Q‖ ^ (n + 1)))) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (fun i => by
      rw [← sub_eq_add_neg]; exact (sub_pos.mpr (pow_succ_lt_one hQ i)).ne') (summable_norm_neg_pow_real hQ)
  simp only [← sub_eq_add_neg] at hne
  have hge : 0 ≤ ∏' n : ℕ, ((1 : ℝ) - ‖Q‖ ^ (n + 1)) :=
    ge_of_tendsto' (multipliable_pfact hQ).tendsto_prod_tprod_nat fun m =>
      Finset.prod_nonneg fun i _ => (sub_pos.mpr (pow_succ_lt_one hQ i)).le
  exact lt_of_le_of_ne hge hne.symm

theorem tprod_pfact_le (hQ : ‖Q‖ < 1) (m : ℕ) :
    (∏' n : ℕ, ((1 : ℝ) - ‖Q‖ ^ (n + 1))) ≤ ∏ i ∈ Finset.range m, (1 - ‖Q‖ ^ (i + 1)) := by
  have hanti : Antitone fun m : ℕ => ∏ i ∈ Finset.range m, ((1 : ℝ) - ‖Q‖ ^ (i + 1)) := by
    refine antitone_nat_of_succ_le fun n => ?_
    rw [Finset.prod_range_succ]
    exact mul_le_of_le_one_right
      (Finset.prod_nonneg fun i _ => (sub_pos.mpr (pow_succ_lt_one hQ i)).le)
      (sub_le_self _ (pow_nonneg (norm_nonneg _) _))
  exact hanti.le_of_tendsto (multipliable_pfact hQ).tendsto_prod_tprod_nat m

theorem le_norm_qfact (hQ : ‖Q‖ < 1) (m : ℕ) :
    (∏' n : ℕ, ((1 : ℝ) - ‖Q‖ ^ (n + 1))) ≤ ‖qfact Q m‖ := by
  refine (tprod_pfact_le hQ m).trans ?_
  rw [qfact, norm_prod]
  refine Finset.prod_le_prod (fun i _ => (sub_pos.mpr (pow_succ_lt_one hQ i)).le) fun i _ => ?_
  have h := norm_sub_norm_le (1 : ℂ) (Q ^ (i + 1))
  rwa [norm_one, norm_pow] at h

theorem norm_qfact_le (hQ : ‖Q‖ < 1) (m : ℕ) :
    ‖qfact Q m‖ ≤ Real.exp (∑' n : ℕ, ‖Q‖ ^ (n + 1)) := by
  rw [qfact, norm_prod]
  calc ∏ i ∈ Finset.range m, ‖(1 : ℂ) - Q ^ (i + 1)‖
      ≤ ∏ i ∈ Finset.range m, (1 + ‖Q‖ ^ (i + 1)) := by
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
        have h := norm_sub_le (1 : ℂ) (Q ^ (i + 1))
        rwa [norm_one, norm_pow] at h
    _ ≤ Real.exp (∑ i ∈ Finset.range m, ‖Q‖ ^ (i + 1)) :=
        Real.prod_one_add_le_exp_sum _ fun i => pow_nonneg (norm_nonneg _) _
    _ ≤ Real.exp (∑' n : ℕ, ‖Q‖ ^ (n + 1)) :=
        Real.exp_le_exp.mpr ((summable_pow_succ hQ).sum_le_tsum _ fun i _ =>
          pow_nonneg (norm_nonneg _) _)

def fam (c : ℕ → ℤ → ℂ) (t : ℤ → ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  if -(N : ℤ) ≤ j ∧ j ≤ N then c N j * t j else 0

theorem sum_Icc_eq_tsum_fam (c : ℕ → ℤ → ℂ) (t : ℤ → ℂ) (N : ℕ) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) N, c N j * t j = ∑' j, fam c t N j := by
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    rw [fam, if_pos hj]
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rw [fam, if_neg hj]

theorem tendsto_sum_Icc (hQ : ‖Q‖ < 1) {t : ℤ → ℂ} (ht : Summable fun j => ‖t j‖)
    (c : ℕ → ℤ → ℂ)
    (hc : ∀ (N : ℕ) (j : ℤ), -(N : ℤ) ≤ j → j ≤ N →
      c N j = qfact Q (2 * N) / (qfact Q (N + j).toNat * qfact Q (N - j).toNat)) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Icc (-(N : ℤ)) N, c N j * t j) atTop
      (𝓝 ((∏' n : ℕ, (1 - Q ^ (n + 1)))⁻¹ * ∑' j : ℤ, t j)) := by
  classical
  have hE0 : (∏' n : ℕ, (1 - Q ^ (n + 1))) ≠ 0 := tprod_one_sub_pow_ne_zero hQ
  have he0 : 0 < ∏' n : ℕ, ((1 : ℝ) - ‖Q‖ ^ (n + 1)) := tprod_pfact_pos hQ
  have hle : ∀ m, (∏' n : ℕ, ((1 : ℝ) - ‖Q‖ ^ (n + 1))) ≤ ‖qfact Q m‖ := le_norm_qfact hQ
  have hP0 : 0 ≤ Real.exp (∑' n : ℕ, ‖Q‖ ^ (n + 1)) := (Real.exp_pos _).le
  have hPle : ∀ m, ‖qfact Q m‖ ≤ Real.exp (∑' n : ℕ, ‖Q‖ ^ (n + 1)) := norm_qfact_le hQ
  set E : ℂ := ∏' n : ℕ, (1 - Q ^ (n + 1))
  set e : ℝ := ∏' n : ℕ, ((1 : ℝ) - ‖Q‖ ^ (n + 1))
  set P : ℝ := Real.exp (∑' n : ℕ, ‖Q‖ ^ (n + 1))
  simp_rw [sum_Icc_eq_tsum_fam c t]
  rw [← tsum_mul_left]
  refine tendsto_tsum_of_dominated_convergence (bound := fun j => P / (e * e) * ‖t j‖)
    (ht.mul_left _) (fun j => ?_) (Eventually.of_forall fun N j => ?_)
  ·
    have h2 : Tendsto (fun N : ℕ => qfact Q (2 * N)) atTop (𝓝 E) :=
      (tendsto_qfact hQ).comp
        (tendsto_atTop_mono (fun N : ℕ => show N ≤ 2 * N by omega) tendsto_id)
    have hp : Tendsto (fun N : ℕ => qfact Q ((N : ℤ) + j).toNat) atTop (𝓝 E) :=
      (tendsto_qfact hQ).comp
        (tendsto_atTop_mono (fun N : ℕ => show N - j.natAbs ≤ ((N : ℤ) + j).toNat by omega)
          (tendsto_sub_atTop_nat j.natAbs))
    have hm : Tendsto (fun N : ℕ => qfact Q ((N : ℤ) - j).toNat) atTop (𝓝 E) :=
      (tendsto_qfact hQ).comp
        (tendsto_atTop_mono (fun N : ℕ => show N - j.natAbs ≤ ((N : ℤ) - j).toNat by omega)
          (tendsto_sub_atTop_nat j.natAbs))
    have hlim : Tendsto (fun N : ℕ => qfact Q (2 * N) /
        (qfact Q ((N : ℤ) + j).toNat * qfact Q ((N : ℤ) - j).toNat) * t j) atTop
        (𝓝 (E / (E * E) * t j)) :=
      (h2.div (hp.mul hm) (mul_ne_zero hE0 hE0)).mul tendsto_const_nhds
    have hEE : E / (E * E) * t j = E⁻¹ * t j := by
      rw [div_eq_mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ hE0, one_mul]
    rw [← hEE]
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop j.natAbs] with N hN
    have h1 : -(N : ℤ) ≤ j := by omega
    have h1' : j ≤ (N : ℤ) := by omega
    rw [fam, if_pos ⟨h1, h1'⟩, hc N j h1 h1']
  ·
    show ‖fam c t N j‖ ≤ P / (e * e) * ‖t j‖
    by_cases h : -(N : ℤ) ≤ j ∧ j ≤ N
    · rw [fam, if_pos h, hc N j h.1 h.2, norm_mul, norm_div, norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact div_le_div₀ hP0 (hPle _) (mul_pos he0 he0)
        (mul_le_mul (hle _) (hle _) he0.le (norm_nonneg _))
    · rw [fam, if_neg h, norm_zero]
      exact mul_nonneg (div_nonneg hP0 (mul_pos he0 he0).le) (norm_nonneg _)

theorem tendsto_sum_range (hQ : ‖Q‖ < 1) {t : ℤ → ℂ} (ht : Summable fun j => ‖t j‖)
    (d : ℕ → ℕ → ℂ)
    (hd : ∀ (N k : ℕ), k ≤ 2 * N → d N k = qfact Q (2 * N) / (qfact Q k * qfact Q (2 * N - k))) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (2 * N + 1), d N k * t ((k : ℤ) - N)) atTop
      (𝓝 ((∏' n : ℕ, (1 - Q ^ (n + 1)))⁻¹ * ∑' j : ℤ, t j)) := by
  have hre : ∀ N : ℕ, ∑ k ∈ Finset.range (2 * N + 1), d N k * t ((k : ℤ) - N)
      = ∑ j ∈ Finset.Icc (-(N : ℤ)) N, d N (j + N).toNat * t j := by
    intro N
    refine Finset.sum_nbij' (fun k => (k : ℤ) - N) (fun j => (j + N).toNat) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_range] at hk
      show (k : ℤ) - N ∈ Finset.Icc (-(N : ℤ)) N
      rw [Finset.mem_Icc]
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      show (j + N).toNat ∈ Finset.range (2 * N + 1)
      rw [Finset.mem_range]
      omega
    · intro k _
      show ((k : ℤ) - N + N).toNat = k
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      show (((j + N).toNat : ℕ) : ℤ) - N = j
      omega
    · intro k _
      show d N k * t ((k : ℤ) - N) = d N ((k : ℤ) - N + N).toNat * t ((k : ℤ) - N)
      rw [show ((k : ℤ) - N + N).toNat = k by omega]
  simp_rw [hre]
  refine tendsto_sum_Icc hQ ht (fun N j => d N (j + N).toNat) fun N j h1 h2 => ?_
  show d N (j + N).toNat = qfact Q (2 * N) / (qfact Q (N + j).toNat * qfact Q (N - j).toNat)
  rw [hd N (j + N).toNat (by omega), show (j + (N : ℤ)).toNat = ((N : ℤ) + j).toNat by rw [add_comm],
    show 2 * N - ((N : ℤ) + j).toNat = ((N : ℤ) - j).toNat by omega]

end JTPTannery
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

end R2
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

section R3
open scoped Real
open Complex

namespace JTPDEngine

variable (τ : ℂ)

private def q : ℂ := Complex.exp (π * I * τ)

private def Q : ℂ := Complex.exp (2 * π * I * τ)

private def w (z : ℂ) : ℂ := Complex.exp (2 * π * I * z)

private lemma q_sq : q τ ^ 2 = Q τ := by
  unfold q Q; rw [← Complex.exp_nat_mul]; ring_nf

omit τ in
private lemma w_ne_zero (z : ℂ) : w z ≠ 0 := Complex.exp_ne_zero _

private lemma q_ne_zero : q τ ≠ 0 := Complex.exp_ne_zero _

private lemma Q_ne_zero : Q τ ≠ 0 := Complex.exp_ne_zero _

private lemma norm_q_lt_one (hτ : 0 < τ.im) : ‖q τ‖ < 1 := by
  unfold q
  rw [Complex.norm_exp]
  have him : (↑π * I * τ).re = -π * τ.im := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  rw [him]
  have : (0 : ℝ) < π * τ.im := mul_pos Real.pi_pos hτ
  exact Real.exp_lt_one_iff.mpr (by linarith)

private lemma norm_Q_lt_one (hτ : 0 < τ.im) : ‖Q τ‖ < 1 := by
  rw [← q_sq, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (norm_q_lt_one τ hτ) two_ne_zero

section TermRw

private lemma fac1_eq (n : ℕ) :
    1 - Complex.exp (2 * π * I * (n + 1) * τ) = 1 - Q τ ^ (n + 1) := by
  unfold Q
  rw [show (2 * π * I * (↑n + 1) * τ : ℂ) = (↑(n + 1 : ℕ) : ℂ) * (2 * π * I * τ) from by
        push_cast; ring, Complex.exp_nat_mul]

private lemma fac2_eq (z : ℂ) (n : ℕ) :
    1 + Complex.exp (π * I * (2 * n + 1) * τ + 2 * π * I * z)
      = 1 + q τ ^ (2 * n + 1) * w z := by
  unfold q w
  rw [show (π * I * (2 * ↑n + 1) * τ + 2 * π * I * z : ℂ)
        = (↑(2 * n + 1 : ℕ) : ℂ) * (π * I * τ) + (2 * π * I * z) from by push_cast; ring,
      Complex.exp_add, Complex.exp_nat_mul]

private lemma fac3_eq (z : ℂ) (n : ℕ) :
    1 + Complex.exp (π * I * (2 * n + 1) * τ - 2 * π * I * z)
      = 1 + q τ ^ (2 * n + 1) * (w z)⁻¹ := by
  unfold q w
  rw [show (π * I * (2 * ↑n + 1) * τ - 2 * π * I * z : ℂ)
        = (↑(2 * n + 1 : ℕ)) * (π * I * τ) + (-(2 * π * I * z)) by push_cast; ring,
    Complex.exp_add, Complex.exp_nat_mul, Complex.exp_neg]

private lemma term_eq_qw (z : ℂ) (j : ℤ) :
    jacobiTheta₂_term j z τ = q τ ^ (j ^ 2) * w z ^ j := by
  unfold jacobiTheta₂_term q w
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1; push_cast; ring

end TermRw
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

section Mult

private lemma summable_Q_pow (hτ : 0 < τ.im) : Summable (fun n : ℕ => ‖Q τ ^ (n + 1)‖) := by
  simp only [norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg _) (norm_Q_lt_one τ hτ)).mul_left ‖Q τ‖
    |>.congr (fun n => by rw [pow_succ'])

private lemma summable_q_odd_mul (hτ : 0 < τ.im) (x : ℂ) :
    Summable (fun n : ℕ => ‖q τ ^ (2 * n + 1) * x‖) := by
  simp only [norm_mul, norm_pow]
  refine Summable.mul_right _ ?_
  have hrw : ∀ n : ℕ, ‖q τ‖ ^ (2 * n + 1) = ‖q τ‖ * (‖q τ‖ ^ 2) ^ n := by
    intro n; rw [← pow_mul, ← pow_succ']
  refine ((summable_geometric_of_lt_one (by positivity) ?_).mul_left ‖q τ‖).congr
    (fun n => (hrw n).symm)
  rw [← norm_pow, q_sq]; exact norm_Q_lt_one τ hτ

private lemma multipliable_Eu (hτ : 0 < τ.im) :
    Multipliable (fun n : ℕ => 1 - Q τ ^ (n + 1)) := by
  refine Complex.multipliable_one_add_of_summable (f := fun n => -(Q τ ^ (n + 1))) ?_ |>.congr
    (fun n => by ring)
  exact (summable_Q_pow τ hτ).of_norm.neg

private lemma multipliable_Pplus (hτ : 0 < τ.im) (x : ℂ) :
    Multipliable (fun n : ℕ => 1 + q τ ^ (2 * n + 1) * x) :=
  Complex.multipliable_one_add_of_summable ((summable_q_odd_mul τ hτ x).of_norm)

end Mult
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

section Split

private def Eu : ℂ := ∏' n : ℕ, (1 - Q τ ^ (n + 1))

private def Pp (x : ℂ) : ℂ := ∏' n : ℕ, (1 + q τ ^ (2 * n + 1) * x)

private lemma statement_RHS_eq (z : ℂ) (hτ : 0 < τ.im) :
    (∏' n : ℕ, ((1 - Complex.exp (2 * π * I * (n + 1) * τ)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ + 2 * π * I * z)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ - 2 * π * I * z))))
      = Eu τ * Pp τ (w z) * Pp τ ((w z)⁻¹) := by
  unfold Eu Pp
  rw [← Multipliable.tprod_mul (multipliable_Eu τ hτ) (multipliable_Pplus τ hτ (w z)),
      ← Multipliable.tprod_mul ((multipliable_Eu τ hτ).mul (multipliable_Pplus τ hτ (w z)))
        (multipliable_Pplus τ hτ ((w z)⁻¹))]
  refine tprod_congr (fun n => ?_)
  rw [fac1_eq τ n, fac2_eq τ z n, fac3_eq τ z n]

end Split
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

section LhsLimit

open Finset in

private def LHS_N (x : ℂ) (N : ℕ) : ℂ :=
  ∏ j ∈ range N, (1 + q τ ^ (2 * j + 1) * x) * (1 + q τ ^ (2 * j + 1) * x⁻¹)

open Finset in
private lemma tendsto_LHS_N (hτ : 0 < τ.im) (x : ℂ) :
    Filter.Tendsto (LHS_N τ x) Filter.atTop (nhds (Pp τ x * Pp τ x⁻¹)) := by
  unfold LHS_N Pp
  have h1 := (multipliable_Pplus τ hτ x).tendsto_prod_tprod_nat
  have h2 := (multipliable_Pplus τ hτ x⁻¹).tendsto_prod_tprod_nat
  have := h1.mul h2
  refine this.congr (fun N => ?_)
  rw [← prod_mul_distrib]

end LhsLimit
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

section Indicator

open Finset in

private lemma sum_eq_tsum_ite (s : Finset ℤ) (a : ℤ → ℂ) :
    ∑ j ∈ s, a j = ∑' j : ℤ, (if j ∈ s then a j else 0) := by
  rw [tsum_eq_sum (s := s)]
  · exact sum_congr rfl (fun j hj => (if_pos hj).symm)
  · intro j hj; exact if_neg hj

end Indicator
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

section Assembly

private theorem theta_eq_Eu_Pp (z : ℂ) (hτ : 0 < τ.im)
    (hEu_ne : Eu τ ≠ 0)
    (hR2 : Filter.Tendsto (LHS_N τ (w z)) Filter.atTop
      (nhds ((Eu τ)⁻¹ * jacobiTheta₂ z τ))) :
    jacobiTheta₂ z τ = Eu τ * Pp τ (w z) * Pp τ ((w z)⁻¹) := by
  have hPP := tendsto_LHS_N τ hτ (w z)
  have heq := tendsto_nhds_unique hR2 hPP

  rw [mul_assoc, ← heq, mul_inv_cancel_left₀ hEu_ne]

open Finset in

private lemma LHS_N_eq_sum_term (z : ℂ) (N : ℕ) (a : ℕ → ℂ)
    (hR1 : ∏ j ∈ range N, ((1 + (w z) * q τ ^ (2*j+1)) * (1 + (w z)⁻¹ * q τ ^ (2*j+1)))
            = ∑ k ∈ range (2*N+1),
                a k * q τ ^ (((k:ℤ) - N)^2) * w z ^ ((k:ℤ) - N)) :
    LHS_N τ (w z) N
      = ∑ k ∈ range (2*N+1), a k * jacobiTheta₂_term ((k:ℤ) - N) z τ := by
  unfold LHS_N
  rw [show ∏ j ∈ range N, (1 + q τ ^ (2*j+1) * w z) * (1 + q τ ^ (2*j+1) * (w z)⁻¹)
        = ∏ j ∈ range N, ((1 + (w z) * q τ ^ (2*j+1)) * (1 + (w z)⁻¹ * q τ ^ (2*j+1))) from
      prod_congr rfl (fun j _ => by ring), hR1]
  refine sum_congr rfl (fun k _ => ?_)
  rw [term_eq_qw τ z ((k:ℤ) - N), mul_assoc]

end Assembly
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

end JTPDEngine
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

open JTPDEngine Finset Filter Topology in
theorem solution (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ = ∏' n : ℕ,
      ((1 - Complex.exp (2 * π * I * (n + 1) * τ)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ + 2 * π * I * z)) *
        (1 + Complex.exp (π * I * (2 * n + 1) * τ - 2 * π * I * z))) := by
  rw [statement_RHS_eq τ z hτ]
  have hQ : ‖Q τ‖ < 1 := norm_Q_lt_one τ hτ
  have hEu_ne : Eu τ ≠ 0 := JTPTannery.tprod_one_sub_pow_ne_zero hQ
  have ht : Summable (fun j : ℤ => ‖jacobiTheta₂_term j z τ‖) :=
    ((summable_jacobiTheta₂_term_iff z τ).mpr hτ).norm
  refine theta_eq_Eu_Pp τ z hτ hEu_ne ?_

  have hTsr := JTPTannery.tendsto_sum_range (Q := Q τ) hQ
    (t := fun j => jacobiTheta₂_term j z τ) ht
    (fun N k => JTPEngine.qbinom (Q τ) (2 * N) k)
    (fun N k hk => if_pos hk)

  refine hTsr.congr (fun N => ?_)
  rw [← LHS_N_eq_sum_term τ z N (fun k => JTPEngine.qbinom (Q τ) (2 * N) k) ?_]

  have hR1 := JTPEngine.finite_jtp (q := q τ) (q_ne_zero τ) (norm_q_lt_one τ hτ)
    (x := w z) (w_ne_zero z) N
  rw [q_sq τ] at hR1
  exact hR1

end R3
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

end
p2m_reactivate "P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine"

end S_jacobiTheta_two_eq_tprod
end P2MW
export P2MW.S_jacobiTheta_two_eq_tprod (solution)
