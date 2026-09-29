-- Prove2me | solution 1 for rademacher_phi_level_congruence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/0d977816-7a1b-52ca-aeeb-51f6073b4f1d

import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_rademacher_phi_level_congruence

set_option autoImplicit false

namespace DedekindSumRows

theorem two_mul_sum_range_natCast (k : ℕ) :
    2 * ∑ r ∈ Finset.range k, (r : ℚ) = k * ((k : ℚ) - 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem six_mul_sum_range_natCast_sq (k : ℕ) :
    6 * ∑ r ∈ Finset.range k, (r : ℚ) ^ 2 = k * ((k : ℚ) - 1) * (2 * k - 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem dedekindSaw_natCast_div_mod (a k : ℕ) :
    dedekindSaw ((a : ℚ) / k) = dedekindSaw (((a % k : ℕ) : ℚ) / k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.mod_zero]
  · have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have h1 : (a : ℚ) = ((a % k : ℕ) : ℚ) + ((a / k : ℕ) : ℚ) * k := by
      exact_mod_cast (Nat.mod_add_div' a k).symm
    rw [h1, add_div, mul_div_cancel_right₀ _ hk0, dedekindSaw_add_natCast]

theorem dedekindSaw_natCast_div_congr {a b k : ℕ} (hab : a ≡ b [MOD k]) :
    dedekindSaw ((a : ℚ) / k) = dedekindSaw ((b : ℚ) / k) := by
  rw [dedekindSaw_natCast_div_mod a k, dedekindSaw_natCast_div_mod b k]
  have h : a % k = b % k := hab
  rw [h]

theorem dedekindSaw_natCast_div_ite {ρ k : ℕ} (hρ : ρ < k) :
    dedekindSaw ((ρ : ℚ) / k) = if ρ = 0 then 0 else (ρ : ℚ) / k - 1 / 2 := by
  rcases eq_or_ne ρ 0 with rfl | h0
  · rw [if_pos rfl, Nat.cast_zero, zero_div, dedekindSaw_zero]
  · rw [if_neg h0, dedekindSaw_natCast_div (Nat.pos_of_ne_zero h0) hρ]

theorem sum_range_mul_mod_of_coprime {M : Type*} [AddCommMonoid M] {h k : ℕ}
    (hco : Nat.Coprime h k) (f : ℕ → M) :
    ∑ r ∈ Finset.range k, f (h * r % k) = ∑ r ∈ Finset.range k, f r := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  rcases eq_or_ne k 1 with rfl | hk1
  · simp [Nat.mod_one, one_smul]
  have hk2 : 1 < k := by omega
  obtain ⟨h', _, hh'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco hk2
  have hmod : h * h' ≡ 1 [MOD k] := by
    show h * h' % k = 1 % k
    rw [hh', Nat.mod_eq_of_lt hk2]
  have key : ∀ m a : ℕ, m * (a % k) % k = m * a % k := fun m a =>
    ((Nat.mod_modEq a k).mul_left m : _)
  refine Finset.sum_nbij' (fun r => h * r % k) (fun r => h' * r % k) ?_ ?_ ?_ ?_ ?_
  · exact fun r _ => Finset.mem_range.2 (Nat.mod_lt _ (by omega))
  · exact fun r _ => Finset.mem_range.2 (Nat.mod_lt _ (by omega))
  · intro r hr
    have hrk := Finset.mem_range.1 hr
    show h' * (h * r % k) % k = r
    have h2 : h * h' * r % k = r := by
      have h3 : h * h' * r % k = 1 * r % k := hmod.mul_right r
      rwa [one_mul, Nat.mod_eq_of_lt hrk] at h3
    calc h' * (h * r % k) % k = h' * (h * r) % k := key h' (h * r)
      _ = h * h' * r % k := by rw [show h' * (h * r) = h * h' * r from by ring]
      _ = r := h2
  · intro r hr
    have hrk := Finset.mem_range.1 hr
    show h * (h' * r % k) % k = r
    have h2 : h * h' * r % k = r := by
      have h3 : h * h' * r % k = 1 * r % k := hmod.mul_right r
      rwa [one_mul, Nat.mod_eq_of_lt hrk] at h3
    calc h * (h' * r % k) % k = h * (h' * r) % k := key h (h' * r)
      _ = h * h' * r % k := by rw [← mul_assoc]
      _ = r := h2
  · exact fun r _ => rfl

theorem six_mul_dedekindSum_sq (h k : ℕ) (hk : 0 < k) :
    6 * (k : ℚ) ^ 2 * dedekindSum h k
      = 6 * (∑ r ∈ Finset.range k, (r : ℚ) * ((h * r % k : ℕ) : ℚ))
        - 3 * (k : ℚ) * (∑ r ∈ Finset.range k, ((h * r % k : ℕ) : ℚ)) := by
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have key : dedekindSum h k = ∑ r ∈ Finset.range k,
      ((if r = 0 then (0 : ℚ) else (r : ℚ) / k - 1 / 2)
        * (if h * r % k = 0 then (0 : ℚ) else ((h * r % k : ℕ) : ℚ) / k - 1 / 2)) := by
    unfold dedekindSum
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrk := Finset.mem_range.1 hr
    have c2arg : ((h : ℤ) : ℚ) * r / k = ((h * r : ℕ) : ℚ) / k := by push_cast; ring
    rw [dedekindSaw_natCast_div_ite hrk, c2arg, dedekindSaw_natCast_div_mod,
      dedekindSaw_natCast_div_ite (Nat.mod_lt _ hk)]
  have hterm : ∀ r ∈ Finset.range k,
      6 * (k : ℚ) ^ 2 * ((if r = 0 then (0 : ℚ) else (r : ℚ) / k - 1 / 2)
          * (if h * r % k = 0 then (0 : ℚ) else ((h * r % k : ℕ) : ℚ) / k - 1 / 2))
      = (6 * ((r : ℚ) * ((h * r % k : ℕ) : ℚ)) - 3 * (k : ℚ) * ((h * r % k : ℕ) : ℚ)
          - 3 * (k : ℚ) * (r : ℚ) + 3 / 2 * (k : ℚ) ^ 2)
        - (if h * r % k = 0 then 3 / 2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) * (r : ℚ) else 0) := by
    intro r hr
    rcases eq_or_ne (h * r % k) 0 with hρ | hρ
    · rcases eq_or_ne r 0 with rfl | hr0
      · rw [if_pos rfl, if_pos hρ, if_pos hρ, hρ]
        push_cast
        ring
      · rw [if_neg hr0, if_pos hρ, if_pos hρ, hρ]
        push_cast
        ring
    · have hr0 : r ≠ 0 := by
        rintro rfl
        exact hρ (by simp)
      rw [if_neg hr0, if_neg hρ, if_neg hρ]
      field_simp
      ring
  have hcorr : ∑ r ∈ Finset.range k,
      (if h * r % k = 0 then 3 / 2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) * (r : ℚ) else 0)
      = 3 / 2 * (k : ℚ) ^ 2 := by
    rw [← Finset.sum_filter]
    have h0mem : 0 ∈ Finset.filter (fun r => h * r % k = 0) (Finset.range k) := by
      simp [Finset.mem_filter, Finset.mem_range, hk]
    rw [← Finset.insert_erase h0mem, Finset.sum_insert (Finset.notMem_erase _ _)]
    have hrest : ∑ r ∈ (Finset.filter (fun r => h * r % k = 0) (Finset.range k)).erase 0,
        (3 / 2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) * (r : ℚ)) = 0 := by
      refine Finset.sum_involution (fun r _ => k - r) ?_ ?_ ?_ ?_
      · intro r hr
        have hrk : r < k := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_erase.1 hr).2).1
        show 3 / 2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) * (r : ℚ)
            + (3 / 2 * (k : ℚ) ^ 2 - 3 * (k : ℚ) * ((k - r : ℕ) : ℚ)) = 0
        rw [Nat.cast_sub hrk.le]
        ring
      · intro r hr hf hgr
        apply hf
        have hrk : r < k := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_erase.1 hr).2).1
        have hgr' : k - r = r := hgr
        have h2r : k = 2 * r := by omega
        rw [h2r]
        push_cast
        ring
      · intro r hr
        obtain ⟨hr0, hmem⟩ := Finset.mem_erase.1 hr
        obtain ⟨hrange, hρ⟩ := Finset.mem_filter.1 hmem
        have hrk : r < k := Finset.mem_range.1 hrange
        have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
        show k - r ∈ (Finset.filter (fun r => h * r % k = 0) (Finset.range k)).erase 0
        refine Finset.mem_erase.2 ⟨by omega, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩⟩
        have hadd : h * (k - r) + h * r = h * k := by
          rw [← mul_add, Nat.sub_add_cancel hrk.le]
        have hstep : h * (k - r) % k = (h * (k - r) + h * r) % k := by
          rw [Nat.add_mod, hρ, add_zero, Nat.mod_mod_of_dvd _ dvd_rfl]
        rw [hstep, hadd, Nat.mul_mod_left]
      · intro r hr
        have hrk : r < k := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_erase.1 hr).2).1
        show k - (k - r) = r
        omega
    rw [hrest, add_zero, Nat.cast_zero]
    ring
  have hmain : ∑ r ∈ Finset.range k,
      (6 * ((r : ℚ) * ((h * r % k : ℕ) : ℚ)) - 3 * (k : ℚ) * ((h * r % k : ℕ) : ℚ)
        - 3 * (k : ℚ) * (r : ℚ) + 3 / 2 * (k : ℚ) ^ 2)
      = 6 * (∑ r ∈ Finset.range k, (r : ℚ) * ((h * r % k : ℕ) : ℚ))
        - 3 * (k : ℚ) * (∑ r ∈ Finset.range k, ((h * r % k : ℕ) : ℚ))
        - 3 * (k : ℚ) * (∑ r ∈ Finset.range k, (r : ℚ)) + 3 / 2 * (k : ℚ) ^ 2 * k := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  rw [key, Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hmain, hcorr]
  linear_combination (-(3 / 2) * (k : ℚ)) * two_mul_sum_range_natCast k

theorem dedekindSum_one_left (k : ℕ) :
    dedekindSum 1 k = ((k : ℚ) - 1) * ((k : ℚ) - 2) / (12 * k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [dedekindSum_zero_right]
    simp
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h6 := six_mul_dedekindSum_sq 1 k hk
  rw [Nat.cast_one] at h6
  have hP : (∑ r ∈ Finset.range k, (r : ℚ) * ((1 * r % k : ℕ) : ℚ))
      = ∑ r ∈ Finset.range k, (r : ℚ) ^ 2 := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [one_mul, Nat.mod_eq_of_lt (Finset.mem_range.1 hr)]
    ring
  have hR : (∑ r ∈ Finset.range k, ((1 * r % k : ℕ) : ℚ)) = ∑ r ∈ Finset.range k, (r : ℚ) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [one_mul, Nat.mod_eq_of_lt (Finset.mem_range.1 hr)]
  rw [hP, hR] at h6
  have hmain : 12 * (k : ℚ) * dedekindSum 1 k = ((k : ℚ) - 1) * ((k : ℚ) - 2) := by
    refine mul_left_cancel₀ hk0 ?_
    linear_combination 2 * h6 - 3 * (k : ℚ) * two_mul_sum_range_natCast k
      + 2 * six_mul_sum_range_natCast_sq k
  rw [eq_div_iff (mul_ne_zero (by norm_num) hk0)]
  linear_combination hmain

theorem dedekindSum_of_mul_modEq_one {h h' k : ℕ} (hh : h * h' ≡ 1 [MOD k]) :
    dedekindSum h' k = dedekindSum h k := by
  rcases eq_or_ne k 0 with rfl | hk0
  · have h1 : h * h' = 1 := by simpa [Nat.ModEq] using hh
    have hh1 : h = 1 := Nat.dvd_one.1 ⟨h', h1.symm⟩
    have hh'1 : h' = 1 := Nat.dvd_one.1 ⟨h, by rw [mul_comm]; exact h1.symm⟩
    rw [hh1, hh'1]
  rcases eq_or_ne k 1 with rfl | hk1
  · rw [dedekindSum_one_right, dedekindSum_one_right]
  have hk2 : 1 < k := by omega
  have hk : 0 < k := by omega
  have hmodeq : h * h' % k = 1 := by
    have h0 : h * h' % k = 1 % k := hh
    rwa [Nat.mod_eq_of_lt hk2] at h0
  have hco : Nat.Coprime h k := by
    obtain ⟨q, hq⟩ : ∃ q, h * h' = k * q + 1 := by
      refine ⟨h * h' / k, ?_⟩
      conv_lhs => rw [← Nat.div_add_mod (h * h') k]
      rw [hmodeq]
    have hdvd1 : Nat.gcd h k ∣ k * q + 1 := hq ▸ Dvd.dvd.mul_right (Nat.gcd_dvd_left h k) h'
    have hdvd2 : Nat.gcd h k ∣ k * q := Dvd.dvd.mul_right (Nat.gcd_dvd_right h k) q
    exact Nat.dvd_one.1 ((Nat.dvd_add_right hdvd2).1 hdvd1)
  have key : ∀ r : ℕ, h' * (h * r % k) ≡ r [MOD k] := by
    intro r
    calc h' * (h * r % k) ≡ h' * (h * r) [MOD k] := (Nat.mod_modEq (h * r) k).mul_left h'
      _ = h * h' * r := by ring
      _ ≡ 1 * r [MOD k] := Nat.ModEq.mul_right r hh
      _ = r := one_mul r
  have hperm := (sum_range_mul_mod_of_coprime hco
    (fun n => dedekindSaw ((n : ℚ) / k) * dedekindSaw (((h' : ℤ) : ℚ) * n / k))).symm
  unfold dedekindSum
  refine hperm.trans (Finset.sum_congr rfl fun r hr => ?_)
  show dedekindSaw (((h * r % k : ℕ) : ℚ) / k)
      * dedekindSaw (((h' : ℤ) : ℚ) * ((h * r % k : ℕ) : ℚ) / k)
    = dedekindSaw ((r : ℚ) / k) * dedekindSaw (((h : ℤ) : ℚ) * r / k)
  have c1 : dedekindSaw (((h * r % k : ℕ) : ℚ) / k) = dedekindSaw (((h : ℤ) : ℚ) * r / k) := by
    rw [show ((h : ℤ) : ℚ) * r / k = ((h * r : ℕ) : ℚ) / k by push_cast; ring]
    exact (dedekindSaw_natCast_div_mod (h * r) k).symm
  have c2 : dedekindSaw (((h' : ℤ) : ℚ) * ((h * r % k : ℕ) : ℚ) / k)
      = dedekindSaw ((r : ℚ) / k) := by
    rw [show ((h' : ℤ) : ℚ) * ((h * r % k : ℕ) : ℚ) / k = ((h' * (h * r % k) : ℕ) : ℚ) / k by
      push_cast; ring]
    exact dedekindSaw_natCast_div_congr (key r)
  rw [c1, c2, mul_comm]

theorem dedekindSum_natCast_sub_one (k : ℕ) :
    dedekindSum ((k : ℤ) - 1) k = -dedekindSum 1 k := by
  have h : (k : ℤ) - 1 = -1 + 1 * k := by ring
  rw [h, dedekindSum_add_mul, dedekindSum_neg]

theorem exists_intCast_eq_six_mul_dedekindSum (h k : ℕ) (hk : 0 < k) :
    ∃ z : ℤ, (z : ℚ) = 6 * k * dedekindSum h k := by
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  refine ⟨(h : ℤ) * ((k : ℤ) - 1) * (2 * (k : ℤ) - 1)
    - 6 * (∑ r ∈ Finset.range k, (r : ℤ) * ((h * r / k : ℕ) : ℤ))
    - 3 * (∑ r ∈ Finset.range k, ((h * r % k : ℕ) : ℤ)), ?_⟩
  have h6 := six_mul_dedekindSum_sq h k hk
  have hq5 : (k : ℚ) * (∑ r ∈ Finset.range k, (r : ℚ) * ((h * r / k : ℕ) : ℚ))
      + (∑ r ∈ Finset.range k, (r : ℚ) * ((h * r % k : ℕ) : ℚ))
      = (h : ℚ) * ∑ r ∈ Finset.range k, (r : ℚ) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hdm : (k : ℚ) * ((h * r / k : ℕ) : ℚ) + ((h * r % k : ℕ) : ℚ) = (h : ℚ) * r := by
      exact_mod_cast Nat.div_add_mod (h * r) k
    linear_combination (r : ℚ) * hdm
  have hS2 := six_mul_sum_range_natCast_sq k
  have hcast : (((h : ℤ) * ((k : ℤ) - 1) * (2 * (k : ℤ) - 1)
      - 6 * (∑ r ∈ Finset.range k, (r : ℤ) * ((h * r / k : ℕ) : ℤ))
      - 3 * (∑ r ∈ Finset.range k, ((h * r % k : ℕ) : ℤ)) : ℤ) : ℚ)
      = (h : ℚ) * ((k : ℚ) - 1) * (2 * (k : ℚ) - 1)
        - 6 * (∑ r ∈ Finset.range k, (r : ℚ) * ((h * r / k : ℕ) : ℚ))
        - 3 * (∑ r ∈ Finset.range k, ((h * r % k : ℕ) : ℚ)) := by
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast, Int.cast_ofNat,
      Int.cast_one]
  rw [hcast]
  refine mul_left_cancel₀ hk0 ?_
  linear_combination -h6 - 6 * hq5 - (h : ℚ) * hS2

theorem natDiv_eq_card_filter {a b c : ℕ} (hb : 0 < b) (hc : a / b < c) :
    a / b = (Finset.filter (fun s => s * b ≤ a) (Finset.Ico 1 c)).card := by
  have hext : Finset.Ico 1 (a / b + 1) = Finset.filter (fun s => s * b ≤ a) (Finset.Ico 1 c) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      have hx : x ≤ a / b := by omega
      exact ⟨⟨h1, by omega⟩, (Nat.le_div_iff_mul_le hb).1 hx⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hx : x ≤ a / b := (Nat.le_div_iff_mul_le hb).2 h3
      exact ⟨h1, by omega⟩
  rw [← hext, Nat.card_Ico]
  exact (Nat.add_sub_cancel (a / b) 1).symm

theorem mul_le_mul_iff_div_succ_le {h k : ℕ} (hco : Nat.Coprime h k) (hh : 0 < h)
    {s : ℕ} (hs1 : 0 < s) (hsh : s < h) (r : ℕ) :
    s * k ≤ h * r ↔ k * s / h + 1 ≤ r := by
  have hne : s * k ≠ h * r := by
    intro heq
    have hdvd : h ∣ s * k := ⟨r, heq⟩
    exact absurd (Nat.le_of_dvd hs1 (hco.dvd_of_dvd_mul_right hdvd)) (by omega)
  constructor
  · intro hle
    by_contra hcon
    have hrψ : r ≤ k * s / h := Nat.lt_succ_iff.1 (not_le.1 hcon)
    have h4 : h * r ≤ h * (k * s / h) := Nat.mul_le_mul_left h hrψ
    have h5 : h * (k * s / h) ≤ k * s := by
      rw [mul_comm]
      exact Nat.div_mul_le_self (k * s) h
    exact hne (le_antisymm hle (by rw [mul_comm s k]; exact h4.trans h5))
  · intro hr1
    have h1 : k * s < h * (k * s / h) + h := by
      conv_lhs => rw [← Nat.div_add_mod (k * s) h]
      exact Nat.add_lt_add_left (Nat.mod_lt _ hh) _
    have h3 : h * (k * s / h + 1) ≤ h * r := Nat.mul_le_mul_left h hr1
    calc s * k = k * s := mul_comm s k
      _ ≤ h * (k * s / h) + h := h1.le
      _ = h * (k * s / h + 1) := by ring
      _ ≤ h * r := h3

theorem swap_count (h k : ℕ) (hco : Nat.Coprime h k) (hh : 0 < h) (hk : 0 < k) :
    2 * (∑ r ∈ Finset.range k, r * (h * r / k)) + (∑ s ∈ Finset.range h, (k * s / h) ^ 2)
      + (∑ s ∈ Finset.range h, (k * s / h)) + 2 * (∑ r ∈ Finset.range k, r)
    = 2 * h * (∑ r ∈ Finset.range k, r) := by

  have hA : (∑ r ∈ Finset.range k, r * (h * r / k))
      = ∑ s ∈ Finset.Ico 1 h, ∑ r ∈ Finset.range k, if s * k ≤ h * r then r else 0 := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hdiv : h * r / k < h := by
      rw [Nat.div_lt_iff_lt_mul hk]
      exact (Nat.mul_lt_mul_left hh).2 (Finset.mem_range.1 hr)
    calc r * (h * r / k)
        = r * (Finset.filter (fun s => s * k ≤ h * r) (Finset.Ico 1 h)).card := by
          rw [← natDiv_eq_card_filter hk hdiv]
      _ = (Finset.filter (fun s => s * k ≤ h * r) (Finset.Ico 1 h)).card * r := mul_comm _ _
      _ = ∑ s ∈ Finset.filter (fun s => s * k ≤ h * r) (Finset.Ico 1 h), r := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = ∑ s ∈ Finset.Ico 1 h, if s * k ≤ h * r then r else 0 := Finset.sum_filter _ _

  have hB : ∀ s ∈ Finset.Ico 1 h,
      (∑ r ∈ Finset.range k, if s * k ≤ h * r then r else 0)
        + (∑ r ∈ Finset.range (k * s / h + 1), r) = ∑ r ∈ Finset.range k, r := by
    intro s hs
    obtain ⟨hs1, hsh⟩ := Finset.mem_Ico.1 hs
    have hψ : k * s / h + 1 ≤ k := by
      have : k * s / h < k := by
        rw [Nat.div_lt_iff_lt_mul hh]
        exact (Nat.mul_lt_mul_left hk).2 hsh
      omega
    have hcond : ∀ r, (if s * k ≤ h * r then r else 0) = if k * s / h + 1 ≤ r then r else 0 := by
      intro r
      rcases Nat.lt_or_ge (h * r) (s * k) with hlt | hle
      · rw [if_neg (not_le.2 hlt), if_neg fun hcon =>
          absurd ((mul_le_mul_iff_div_succ_le hco hh hs1 hsh r).2 hcon) (not_le.2 hlt)]
      · rw [if_pos hle, if_pos ((mul_le_mul_iff_div_succ_le hco hh hs1 hsh r).1 hle)]
    rw [Finset.sum_congr rfl fun r _ => hcond r, ← Finset.sum_filter,
      Finset.range_eq_Ico, Finset.Ico_filter_le_of_left_le (Nat.zero_le _)]
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive (fun r => r) (Nat.zero_le _) hψ]
    ring

  have hC : (∑ r ∈ Finset.range k, r * (h * r / k))
      + (∑ s ∈ Finset.Ico 1 h, ∑ r ∈ Finset.range (k * s / h + 1), r)
      = (h - 1) * ∑ r ∈ Finset.range k, r := by
    rw [hA, ← Finset.sum_add_distrib, Finset.sum_congr rfl hB, Finset.sum_const,
      Nat.card_Ico, smul_eq_mul]

  have hD : ∀ m : ℕ, 2 * ∑ r ∈ Finset.range (m + 1), r = m ^ 2 + m := by
    intro m
    calc 2 * ∑ r ∈ Finset.range (m + 1), r
        = (∑ r ∈ Finset.range (m + 1), r) * 2 := mul_comm _ _
      _ = (m + 1) * ((m + 1) - 1) := Finset.sum_range_id_mul_two (m + 1)
      _ = (m + 1) * m := by rw [Nat.add_sub_cancel]
      _ = m ^ 2 + m := by ring

  have hzero : (k * 0 / h) = 0 := by simp
  have hIco : ∀ f : ℕ → ℕ, f 0 = 0 →
      (∑ s ∈ Finset.Ico 1 h, f s) = ∑ s ∈ Finset.range h, f s := by
    intro f hf
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hh, hf, zero_add, zero_add]
  have hsq : (∑ s ∈ Finset.Ico 1 h, (k * s / h) ^ 2) = ∑ s ∈ Finset.range h, (k * s / h) ^ 2 :=
    hIco _ (by simp)
  have hlin : (∑ s ∈ Finset.Ico 1 h, (k * s / h)) = ∑ s ∈ Finset.range h, (k * s / h) :=
    hIco _ (by simp)
  have htri : 2 * (∑ s ∈ Finset.Ico 1 h, ∑ r ∈ Finset.range (k * s / h + 1), r)
      = (∑ s ∈ Finset.Ico 1 h, (k * s / h) ^ 2) + ∑ s ∈ Finset.Ico 1 h, (k * s / h) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => hD (k * s / h)
  have hfinal := congrArg (2 * ·) hC
  rw [mul_add, htri, hsq, hlin] at hfinal
  have h1 : h - 1 + 1 = h := by omega
  calc 2 * (∑ r ∈ Finset.range k, r * (h * r / k)) + (∑ s ∈ Finset.range h, (k * s / h) ^ 2)
        + (∑ s ∈ Finset.range h, (k * s / h)) + 2 * (∑ r ∈ Finset.range k, r)
      = 2 * ((h - 1) * ∑ r ∈ Finset.range k, r) + 2 * (∑ r ∈ Finset.range k, r) := by
        rw [← hfinal]; ring
    _ = 2 * ((h - 1 + 1) * ∑ r ∈ Finset.range k, r) := by ring
    _ = 2 * h * (∑ r ∈ Finset.range k, r) := by rw [h1]; ring

theorem dedekindSum_add_dedekindSum (h k : ℕ) (hh : 0 < h) (hk : 0 < k)
    (hco : Nat.Coprime h k) :
    dedekindSum h k + dedekindSum k h
      = ((h : ℚ) / k + (k : ℚ) / h + 1 / ((h : ℚ) * k)) / 12 - 1 / 4 := by
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hh0 : (h : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hh.ne'

  have e1 := six_mul_dedekindSum_sq h k hk
  have e2 := six_mul_dedekindSum_sq k h hh
  have hperm : (∑ r ∈ Finset.range k, ((h * r % k : ℕ) : ℚ)) = ∑ r ∈ Finset.range k, (r : ℚ) :=
    sum_range_mul_mod_of_coprime hco (fun n => (n : ℚ))
  have hperm' : (∑ s ∈ Finset.range h, ((k * s % h : ℕ) : ℚ)) = ∑ s ∈ Finset.range h, (s : ℚ) :=
    sum_range_mul_mod_of_coprime hco.symm (fun n => (n : ℚ))
  have hperm2 : (∑ r ∈ Finset.range k, ((h * r % k : ℕ) : ℚ) ^ 2)
      = ∑ r ∈ Finset.range k, (r : ℚ) ^ 2 :=
    sum_range_mul_mod_of_coprime hco (fun n => (n : ℚ) ^ 2)
  rw [hperm] at e1
  rw [hperm'] at e2

  have hdm : ∀ r : ℕ, (k : ℚ) * ((h * r / k : ℕ) : ℚ) + ((h * r % k : ℕ) : ℚ) = (h : ℚ) * r :=
    fun r => by exact_mod_cast Nat.div_add_mod (h * r) k
  have hdm' : ∀ s : ℕ, (h : ℚ) * ((k * s / h : ℕ) : ℚ) + ((k * s % h : ℕ) : ℚ) = (k : ℚ) * s :=
    fun s => by exact_mod_cast Nat.div_add_mod (k * s) h

  have e3 : (k : ℚ) * (∑ r ∈ Finset.range k, (r : ℚ) * ((h * r / k : ℕ) : ℚ))
      + (∑ r ∈ Finset.range k, (r : ℚ) * ((h * r % k : ℕ) : ℚ))
      = (h : ℚ) * ∑ r ∈ Finset.range k, (r : ℚ) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by linear_combination (r : ℚ) * hdm r
  have e4 : (h : ℚ) * (∑ s ∈ Finset.range h, (s : ℚ) * ((k * s / h : ℕ) : ℚ))
      + (∑ s ∈ Finset.range h, (s : ℚ) * ((k * s % h : ℕ) : ℚ))
      = (k : ℚ) * ∑ s ∈ Finset.range h, (s : ℚ) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by linear_combination (s : ℚ) * hdm' s

  have e5 : (h : ℚ) ^ 2 * (∑ r ∈ Finset.range k, (r : ℚ) ^ 2)
      = (k : ℚ) ^ 2 * (∑ r ∈ Finset.range k, ((h * r / k : ℕ) : ℚ) ^ 2)
        + 2 * (k : ℚ) * (∑ r ∈ Finset.range k, ((h * r / k : ℕ) : ℚ) * ((h * r % k : ℕ) : ℚ))
        + ∑ r ∈ Finset.range k, ((h * r % k : ℕ) : ℚ) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by
      linear_combination (-((h : ℚ) * r + (k : ℚ) * ((h * r / k : ℕ) : ℚ)
        + ((h * r % k : ℕ) : ℚ))) * hdm r
  rw [hperm2] at e5

  have e6 : (h : ℚ) * (∑ r ∈ Finset.range k, (r : ℚ) * ((h * r / k : ℕ) : ℚ))
      = (k : ℚ) * (∑ r ∈ Finset.range k, ((h * r / k : ℕ) : ℚ) ^ 2)
        + ∑ r ∈ Finset.range k, ((h * r / k : ℕ) : ℚ) * ((h * r % k : ℕ) : ℚ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by
      linear_combination (-((h * r / k : ℕ) : ℚ)) * hdm r

  have e7 : (h : ℚ) * (∑ r ∈ Finset.range k, (r : ℚ))
      = (k : ℚ) * (∑ r ∈ Finset.range k, ((h * r / k : ℕ) : ℚ))
        + ∑ r ∈ Finset.range k, ((h * r % k : ℕ) : ℚ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by linear_combination (-1 : ℚ) * hdm r
  rw [hperm] at e7

  have e8 : 2 * (∑ s ∈ Finset.range h, (s : ℚ) * ((k * s / h : ℕ) : ℚ))
      + (∑ r ∈ Finset.range k, ((h * r / k : ℕ) : ℚ) ^ 2)
      + (∑ r ∈ Finset.range k, ((h * r / k : ℕ) : ℚ))
      + 2 * (∑ s ∈ Finset.range h, (s : ℚ))
      = 2 * (k : ℚ) * ∑ s ∈ Finset.range h, (s : ℚ) := by
    have h8 := congrArg (Nat.cast : ℕ → ℚ) (swap_count k h hco.symm hk hh)
    push_cast at h8
    linear_combination h8

  have e9 := two_mul_sum_range_natCast k
  have e10 := two_mul_sum_range_natCast h
  have e11 := six_mul_sum_range_natCast_sq k
  have e12 := six_mul_sum_range_natCast_sq h

  have hmain : 12 * (h : ℚ) ^ 2 * (k : ℚ) ^ 2 * (dedekindSum h k + dedekindSum k h)
      = (h : ℚ) ^ 3 * k + (h : ℚ) * (k : ℚ) ^ 3 + (h : ℚ) * k
        - 3 * (h : ℚ) ^ 2 * (k : ℚ) ^ 2 := by
    linear_combination 2 * (h : ℚ) ^ 2 * e1 + 2 * (k : ℚ) ^ 2 * e2 + 12 * (h : ℚ) ^ 2 * e3
      + 12 * (k : ℚ) ^ 2 * e4 + 6 * (h : ℚ) * e5 - 12 * (h : ℚ) * (k : ℚ) * e6
      - 6 * (h : ℚ) * (k : ℚ) * e7 - 6 * (h : ℚ) * (k : ℚ) ^ 2 * e8 - 3 * (h : ℚ) * (k : ℚ) * e9
      + (3 * (h : ℚ) * (k : ℚ) ^ 2 - 6 * (h : ℚ) * (k : ℚ) ^ 3) * e10
      + ((h : ℚ) ^ 3 + (h : ℚ)) * e11 + 2 * (k : ℚ) ^ 3 * e12
  have hRHS : ((h : ℚ) / k + (k : ℚ) / h + 1 / ((h : ℚ) * k)) / 12 - 1 / 4
      = ((h : ℚ) ^ 3 * k + (h : ℚ) * (k : ℚ) ^ 3 + (h : ℚ) * k
          - 3 * (h : ℚ) ^ 2 * (k : ℚ) ^ 2) / (12 * (h : ℚ) ^ 2 * (k : ℚ) ^ 2) := by
    field_simp
    ring
  rw [hRHS, eq_div_iff (by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hh0)) (pow_ne_zero 2 hk0))]
  linear_combination hmain

theorem exists_intCast_eq_twelve_mul_dedekindSum (d : ℤ) (c : ℕ) (hc : 0 < c) :
    ∃ t : ℤ, (t : ℚ) = 12 * c * dedekindSum d c := by
  rcases Int.natAbs_eq d with h | h
  · obtain ⟨z, hz⟩ := exists_intCast_eq_six_mul_dedekindSum d.natAbs c hc
    refine ⟨2 * z, ?_⟩
    rw [h]
    push_cast at hz ⊢
    linear_combination 2 * hz
  · obtain ⟨z, hz⟩ := exists_intCast_eq_six_mul_dedekindSum d.natAbs c hc
    refine ⟨-(2 * z), ?_⟩
    rw [h, dedekindSum_neg]
    push_cast at hz ⊢
    linear_combination -2 * hz

theorem twelve_mul_mul_dedekindSum_core {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hco : Nat.Coprime h k) :
    ∃ w : ℤ, 12 * (h : ℚ) * k * dedekindSum h k = (h : ℚ) ^ 2 + 1 + k * w := by
  obtain ⟨z, hz⟩ := exists_intCast_eq_six_mul_dedekindSum k h hh
  have hrec := dedekindSum_add_dedekindSum h k hh hk hco
  have hh0 : (h : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hh.ne'
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  refine ⟨k - 3 * h - 2 * z, ?_⟩
  have hmul : 12 * (h : ℚ) * k * (dedekindSum h k + dedekindSum k h)
      = (h : ℚ) ^ 2 + (k : ℚ) ^ 2 + 1 - 3 * h * k := by
    rw [hrec]
    field_simp
    ring
  push_cast
  linear_combination hmul + 2 * (k : ℚ) * hz

theorem twelve_mul_mul_dedekindSum_eq_sq_add_one_add_mul (d : ℤ) (c : ℕ) (hc : 0 < c)
    (hco : Int.gcd d c = 1) :
    ∃ w : ℤ, 12 * (d : ℚ) * c * dedekindSum d c = (d : ℚ) ^ 2 + 1 + c * w := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hc.ne') with h1 | h2
  ·
    refine ⟨-(d ^ 2 + 1), ?_⟩
    rw [← h1, dedekindSum_one_right]
    push_cast
    ring
  ·
    have hc0 : (c : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hc.ne'
    have hcpos : (0 : ℤ) < c := Int.natCast_pos.2 hc
    set q : ℤ := d / c with hq
    set r : ℤ := d % c with hr
    have hdqr : d = c * q + r := (Int.mul_ediv_add_emod d c).symm
    have hr0 : 0 ≤ r := Int.emod_nonneg d hc0
    have hrc : r < c := Int.emod_lt_of_pos d hcpos
    have hrne : r ≠ 0 := by
      intro h0
      have hdvd : (c : ℤ) ∣ d := ⟨q, by rw [hdqr, h0, add_zero]⟩
      have hg : c ∣ Int.gcd d c := Int.dvd_gcd hdvd dvd_rfl
      rw [hco] at hg
      have := Nat.le_of_dvd one_pos hg
      omega
    set rn : ℕ := r.toNat with hrn
    have hrcast : (rn : ℤ) = r := Int.toNat_of_nonneg hr0
    have hrnpos : 0 < rn := by omega
    have hrnc : rn < c := by omega
    have hcor : Nat.Coprime rn c := by
      have hg1 : Int.gcd r c = 1 := by
        have hg2 : Int.gcd (r + q * c) c = 1 := by
          rw [show r + q * c = c * q + r from by ring, ← hdqr]; exact hco
        rwa [Int.gcd_comm, Int.gcd_add_mul_right_right, Int.gcd_comm] at hg2
      rwa [← hrcast, Int.gcd_natCast_natCast] at hg1
    obtain ⟨w0, hw0⟩ := twelve_mul_mul_dedekindSum_core hrnpos hc hcor
    obtain ⟨t, ht⟩ := exists_intCast_eq_twelve_mul_dedekindSum rn c hc
    have hper : dedekindSum d c = dedekindSum rn c := by
      have hd2 : d = (rn : ℤ) + q * c := by rw [hrcast, hdqr]; ring
      rw [hd2, dedekindSum_add_mul]
    refine ⟨q * t + w0 - c * q ^ 2 - 2 * q * rn, ?_⟩
    rw [hper]
    have hd' : (d : ℚ) = (c : ℚ) * (q : ℚ) + (rn : ℚ) := by
      have : ((c * q + (rn : ℤ) : ℤ) : ℚ) = (d : ℚ) := by
        rw [hrcast, ← hdqr]
      push_cast at this
      linarith [this]
    push_cast
    rw [hd']
    linear_combination hw0 - (q : ℚ) * (c : ℚ) * ht

section Closures

private lemma closure3 : ∀ A B C Q R : ZMod 3, A * R - (B - Q * A) * C = 1 →
    ((A + (C * Q + R)) * C - B * (C * Q + R) * (C ^ 2 - 1))
      - (((B - Q * A) + -C) * R - (-A) * (-C) * (R ^ 2 - 1)) - 3 - Q = 0 := by decide

private lemma closure4_oo : ∀ A B T Q U : ZMod 4,
    A * (2 * U + 1) - (B - Q * A) * (2 * T + 1) = 1 →
    ((A + ((2 * T + 1) * Q + (2 * U + 1))) * (2 * T + 1)
        - B * ((2 * T + 1) * Q + (2 * U + 1)) * ((2 * T + 1) ^ 2 - 1) - 3 * (2 * T + 1) + 3)
      - (((B - Q * A) + -(2 * T + 1)) * (2 * U + 1)
        - (-A) * (-(2 * T + 1)) * ((2 * U + 1) ^ 2 - 1) - 3 * (2 * U + 1) + 3) - 3 - Q = 0 := by
  decide

private lemma closure4_oe : ∀ A B T Q U : ZMod 4,
    A * (2 * U) - (B - Q * A) * (2 * T + 1) = 1 →
    ((A + ((2 * T + 1) * Q + 2 * U)) * (2 * T + 1)
        - B * ((2 * T + 1) * Q + 2 * U) * ((2 * T + 1) ^ 2 - 1) - 3 * (2 * T + 1) + 3)
      - (((B - Q * A) + -(2 * T + 1)) * (2 * U)
        - (-A) * (-(2 * T + 1)) * ((2 * U) ^ 2 - 1) + 3 * -(2 * T + 1)
        - 3 * (2 * U) * -(2 * T + 1))
      - 3 - Q = 0 := by decide

private lemma closure4_eo : ∀ A B T Q U : ZMod 4,
    A * (2 * U + 1) - (B - Q * A) * (2 * T) = 1 →
    ((A + (2 * T * Q + (2 * U + 1))) * (2 * T)
        - B * (2 * T * Q + (2 * U + 1)) * ((2 * T) ^ 2 - 1)
        + 3 * (2 * T * Q + (2 * U + 1)) - 3 * (2 * T) * (2 * T * Q + (2 * U + 1)))
      - (((B - Q * A) + -(2 * T)) * (2 * U + 1)
        - (-A) * (-(2 * T)) * ((2 * U + 1) ^ 2 - 1) - 3 * (2 * U + 1) + 3) - 3 - Q = 0 := by
  decide

end Closures

section PhiDescent

private theorem radPhi_descent_key (c : ℕ) (hc2 : 2 ≤ c) (a b d : ℤ)
    (hdet : a * d - b * c = 1) {q : ℤ} {rn : ℕ}
    (hd3 : d = c * q + rn) (hrnpos : 0 < rn) (_hrnc : rn < c) :
    ((a + d : ℤ) : ℚ) / c - 12 * dedekindSum d c
      = ((b - q * a + -(c : ℤ) : ℤ) : ℚ) / rn - 12 * dedekindSum (-(c : ℤ)) rn + 3 + q := by
  have hcpos : 0 < c := by omega
  have hc0 : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hcpos.ne'
  have hr0 : (rn : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hrnpos.ne'
  have hdet3 : a * rn - (b - q * a) * c = 1 := by
    rw [hd3] at hdet
    linear_combination hdet
  have hcor : Nat.Coprime rn c := by
    have hgd : (Int.gcd (rn : ℤ) c : ℤ) ∣ a * rn - (b - q * a) * c :=
      dvd_sub (Dvd.dvd.mul_left (Int.gcd_dvd_left (rn : ℤ) c) a)
        (Dvd.dvd.mul_left (Int.gcd_dvd_right (rn : ℤ) c) (b - q * a))
    rw [hdet3] at hgd
    have hg1 : Int.gcd (rn : ℤ) c ∣ 1 := by exact_mod_cast hgd
    have hg2 : Int.gcd (rn : ℤ) c = 1 := Nat.dvd_one.mp hg1
    rwa [Int.gcd_natCast_natCast] at hg2

  have hper : dedekindSum d c = dedekindSum rn c := by
    have hd2 : d = (rn : ℤ) + q * c := by rw [hd3]; ring
    rw [hd2, dedekindSum_add_mul]

  have hrec := dedekindSum_add_dedekindSum rn c hrnpos hcpos hcor
  have hneg : dedekindSum (-(c : ℤ)) rn = -dedekindSum c rn := dedekindSum_neg c rn
  have hdetq : (a : ℚ) * rn - (b - q * a) * c = 1 := by exact_mod_cast hdet3
  have hrec12 : 12 * (c : ℚ) * rn * (dedekindSum rn c + dedekindSum c rn)
      = (rn : ℚ) ^ 2 + (c : ℚ) ^ 2 + 1 - 3 * c * rn := by
    rw [hrec]
    field_simp
    ring
  rw [hper, hneg]
  push_cast
  rw [hd3]
  push_cast
  field_simp
  linear_combination (-1 : ℚ) * hrec12 + hdetq

private theorem radPhi_descent_setup (c : ℕ) (hc2 : 2 ≤ c) (a b d : ℤ)
    (hdet : a * d - b * c = 1) :
    ∃ (q : ℤ) (rn : ℕ), d = c * q + rn ∧ 0 < rn ∧ rn < c ∧
      a * rn - (b - q * a) * c = 1 := by
  have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have hcpos : (0 : ℤ) < c := by exact_mod_cast (by omega : 0 < c)
  refine ⟨d / c, (d % c).toNat, ?_, ?_, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg d hc0)]
    exact (Int.mul_ediv_add_emod d c).symm
  · have hr0 : 0 ≤ d % c := Int.emod_nonneg d hc0
    rcases eq_or_lt_of_le hr0 with h0 | h0
    · exfalso
      have hdvd : (c : ℤ) ∣ d := Int.dvd_of_emod_eq_zero h0.symm
      obtain ⟨e, he⟩ := hdvd
      have : (c : ℤ) * (a * e - b) = 1 := by rw [he] at hdet; linear_combination hdet
      have h1 : (c : ℤ) ∣ 1 := ⟨a * e - b, this.symm⟩
      have := Int.le_of_dvd one_pos h1
      omega
    · omega
  · have := Int.emod_lt_of_pos d hcpos
    omega
  · have hr : ((d % c).toNat : ℤ) = d % c := Int.toNat_of_nonneg (Int.emod_nonneg d hc0)
    have hd3 : d = c * (d / c) + ((d % c).toNat : ℤ) := by
      rw [hr]; exact (Int.mul_ediv_add_emod d c).symm
    rw [hd3] at hdet
    linear_combination hdet

theorem radPhi_modThree : ∀ (c : ℕ), 0 < c → ∀ a b d : ℤ, a * d - b * c = 1 →
    ∃ m : ℤ, ((a + d : ℤ) : ℚ) / c - 12 * dedekindSum d c
      = (((a + d) * c - b * d * ((c : ℤ) ^ 2 - 1) + 3 * m : ℤ) : ℚ) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc a b d hdet
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hc.ne') with h1 | h2
    · refine ⟨0, ?_⟩
      rw [← h1, dedekindSum_one_right]
      push_cast
      ring
    · have hc2 : 2 ≤ c := h2
      obtain ⟨q, rn, hd3, hrnpos, hrnc, hdet3⟩ := radPhi_descent_setup c hc2 a b d hdet
      have hkey := radPhi_descent_key c hc2 a b d hdet hd3 hrnpos hrnc
      obtain ⟨m0, hm0⟩ := ih rn hrnc hrnpos (b - q * a) (-a) (-(c : ℤ))
        (by linear_combination hdet3)
      have hdvd : (3 : ℤ) ∣ ((a + d) * c - b * d * ((c : ℤ) ^ 2 - 1)
          - ((b - q * a + -(c : ℤ)) * rn - (-a) * (-(c : ℤ)) * ((rn : ℤ) ^ 2 - 1)) - 3 - q) := by
        have h0 : (((a + d) * c - b * d * ((c : ℤ) ^ 2 - 1)
            - ((b - q * a + -(c : ℤ)) * rn - (-a) * (-(c : ℤ)) * ((rn : ℤ) ^ 2 - 1)) - 3 - q : ℤ)
            : ZMod 3) = 0 := by
          have hd3c : ((d : ℤ) : ZMod 3) = (c : ZMod 3) * ((q : ℤ) : ZMod 3) + (rn : ZMod 3) := by
            have h := congrArg (fun t : ℤ => (t : ZMod 3)) hd3
            push_cast at h ⊢
            exact h
          have hdetc : ((a : ℤ) : ZMod 3) * (rn : ZMod 3)
              - (((b : ℤ) : ZMod 3) - ((q : ℤ) : ZMod 3) * ((a : ℤ) : ZMod 3)) * (c : ZMod 3)
              = 1 := by
            have h := congrArg (fun t : ℤ => (t : ZMod 3)) hdet3
            push_cast at h ⊢
            linear_combination h
          push_cast
          rw [hd3c]
          linear_combination closure3 ((a : ℤ) : ZMod 3) ((b : ℤ) : ZMod 3) (c : ZMod 3)
            ((q : ℤ) : ZMod 3) (rn : ZMod 3) hdetc
        have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h0
        exact_mod_cast h1
      obtain ⟨j, hj⟩ := hdvd
      refine ⟨m0 - j, ?_⟩
      rw [hkey, hm0]
      have hjq := congrArg (fun t : ℤ => (t : ℚ)) hj
      push_cast at hjq ⊢
      linear_combination (-1 : ℚ) * hjq

theorem radPhi_modFour : ∀ (c : ℕ), 0 < c → ∀ a b d : ℤ, a * d - b * c = 1 →
    (Odd c → ∃ m : ℤ, ((a + d : ℤ) : ℚ) / c - 12 * dedekindSum d c
      = (((a + d) * c - b * d * ((c : ℤ) ^ 2 - 1) - 3 * c + 3 + 4 * m : ℤ) : ℚ)) ∧
    (Even c → ∃ m : ℤ, ((a + d : ℤ) : ℚ) / c - 12 * dedekindSum d c
      = (((a + d) * c - b * d * ((c : ℤ) ^ 2 - 1) + 3 * d - 3 * c * d + 4 * m : ℤ) : ℚ)) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc a b d hdet
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hc.ne') with h1 | h2
    · constructor
      · intro _
        refine ⟨0, ?_⟩
        rw [← h1, dedekindSum_one_right]
        push_cast
        ring
      · intro he
        rw [← h1] at he
        exact absurd he (by decide)
    · have hc2 : 2 ≤ c := h2
      obtain ⟨q, rn, hd3, hrnpos, hrnc, hdet3⟩ := radPhi_descent_setup c hc2 a b d hdet
      have hkey := radPhi_descent_key c hc2 a b d hdet hd3 hrnpos hrnc
      have hdet4 : (b - q * a) * (-(c : ℤ)) - (-a) * rn = 1 := by linear_combination hdet3
      constructor
      ·
        intro hodd
        obtain ⟨tc, htc⟩ := hodd
        have hcc : ((c : ℕ) : ZMod 4) = 2 * ((tc : ℕ) : ZMod 4) + 1 := by
          have h := congrArg (fun t : ℕ => (t : ZMod 4)) htc
          push_cast at h
          linear_combination h
        rcases Nat.even_or_odd rn with hre | hro
        ·
          obtain ⟨m0, hm0⟩ := (ih rn hrnc hrnpos (b - q * a) (-a) (-(c : ℤ)) hdet4).2 hre
          obtain ⟨tu, htu⟩ := hre
          have hrr : ((rn : ℕ) : ZMod 4) = 2 * ((tu : ℕ) : ZMod 4) := by
            have h := congrArg (fun t : ℕ => (t : ZMod 4)) htu
            push_cast at h
            linear_combination h
          have hdvd : (4 : ℤ) ∣ ((a + d) * c - b * d * ((c : ℤ) ^ 2 - 1) - 3 * c + 3
              - ((b - q * a + -(c : ℤ)) * rn - (-a) * (-(c : ℤ)) * ((rn : ℤ) ^ 2 - 1)
                 + 3 * (-(c : ℤ)) - 3 * rn * (-(c : ℤ))) - 3 - q) := by
            have h0 : (((a + d) * c - b * d * ((c : ℤ) ^ 2 - 1) - 3 * c + 3
                - ((b - q * a + -(c : ℤ)) * rn - (-a) * (-(c : ℤ)) * ((rn : ℤ) ^ 2 - 1)
                   + 3 * (-(c : ℤ)) - 3 * rn * (-(c : ℤ))) - 3 - q : ℤ) : ZMod 4) = 0 := by
              have hd3c : ((d : ℤ) : ZMod 4)
                  = (c : ZMod 4) * ((q : ℤ) : ZMod 4) + (rn : ZMod 4) := by
                have h := congrArg (fun t : ℤ => (t : ZMod 4)) hd3
                push_cast at h ⊢
                exact h
              have hdetc : ((a : ℤ) : ZMod 4) * (2 * ((tu : ℕ) : ZMod 4))
                  - (((b : ℤ) : ZMod 4) - ((q : ℤ) : ZMod 4) * ((a : ℤ) : ZMod 4))
                    * (2 * ((tc : ℕ) : ZMod 4) + 1) = 1 := by
                have h := congrArg (fun t : ℤ => (t : ZMod 4)) hdet3
                push_cast at h
                rw [hcc, hrr] at h
                linear_combination h
              push_cast
              rw [hd3c, hcc, hrr]
              linear_combination closure4_oe ((a : ℤ) : ZMod 4) ((b : ℤ) : ZMod 4)
                ((tc : ℕ) : ZMod 4) ((q : ℤ) : ZMod 4) ((tu : ℕ) : ZMod 4) hdetc
            have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1 h0
            exact_mod_cast h1
          obtain ⟨j, hj⟩ := hdvd
          refine ⟨m0 - j, ?_⟩
          rw [hkey, hm0]
          have hjq := congrArg (fun t : ℤ => (t : ℚ)) hj
          push_cast at hjq ⊢
          linear_combination (-1 : ℚ) * hjq
        ·
          obtain ⟨m0, hm0⟩ := (ih rn hrnc hrnpos (b - q * a) (-a) (-(c : ℤ)) hdet4).1 hro
          obtain ⟨tu, htu⟩ := hro
          have hrr : ((rn : ℕ) : ZMod 4) = 2 * ((tu : ℕ) : ZMod 4) + 1 := by
            have h := congrArg (fun t : ℕ => (t : ZMod 4)) htu
            push_cast at h
            linear_combination h
          have hdvd : (4 : ℤ) ∣ ((a + d) * c - b * d * ((c : ℤ) ^ 2 - 1) - 3 * c + 3
              - ((b - q * a + -(c : ℤ)) * rn - (-a) * (-(c : ℤ)) * ((rn : ℤ) ^ 2 - 1)
                 - 3 * rn + 3) - 3 - q) := by
            have h0 : (((a + d) * c - b * d * ((c : ℤ) ^ 2 - 1) - 3 * c + 3
                - ((b - q * a + -(c : ℤ)) * rn - (-a) * (-(c : ℤ)) * ((rn : ℤ) ^ 2 - 1)
                   - 3 * rn + 3) - 3 - q : ℤ) : ZMod 4) = 0 := by
              have hd3c : ((d : ℤ) : ZMod 4)
                  = (c : ZMod 4) * ((q : ℤ) : ZMod 4) + (rn : ZMod 4) := by
                have h := congrArg (fun t : ℤ => (t : ZMod 4)) hd3
                push_cast at h ⊢
                exact h
              have hdetc : ((a : ℤ) : ZMod 4) * (2 * ((tu : ℕ) : ZMod 4) + 1)
                  - (((b : ℤ) : ZMod 4) - ((q : ℤ) : ZMod 4) * ((a : ℤ) : ZMod 4))
                    * (2 * ((tc : ℕ) : ZMod 4) + 1) = 1 := by
                have h := congrArg (fun t : ℤ => (t : ZMod 4)) hdet3
                push_cast at h
                rw [hcc, hrr] at h
                linear_combination h
              push_cast
              rw [hd3c, hcc, hrr]
              linear_combination closure4_oo ((a : ℤ) : ZMod 4) ((b : ℤ) : ZMod 4)
                ((tc : ℕ) : ZMod 4) ((q : ℤ) : ZMod 4) ((tu : ℕ) : ZMod 4) hdetc
            have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1 h0
            exact_mod_cast h1
          obtain ⟨j, hj⟩ := hdvd
          refine ⟨m0 - j, ?_⟩
          rw [hkey, hm0]
          have hjq := congrArg (fun t : ℤ => (t : ℚ)) hj
          push_cast at hjq ⊢
          linear_combination (-1 : ℚ) * hjq
      ·
        intro heven
        obtain ⟨tc, htc⟩ := heven
        have hcc : ((c : ℕ) : ZMod 4) = 2 * ((tc : ℕ) : ZMod 4) := by
          have h := congrArg (fun t : ℕ => (t : ZMod 4)) htc
          push_cast at h
          linear_combination h
        have hro : Odd rn := by
          rcases Nat.even_or_odd rn with hre | hro
          · exfalso
            obtain ⟨u, hu⟩ := hre
            have h := congrArg (fun t : ℤ => (t : ZMod 2)) hdet3
            push_cast at h
            have hrn2 : ((rn : ℕ) : ZMod 2) = ((u : ℕ) : ZMod 2) + ((u : ℕ) : ZMod 2) := by
              have h' := congrArg (fun t : ℕ => (t : ZMod 2)) hu
              push_cast at h'
              exact h'
            have hc2' : ((c : ℕ) : ZMod 2) = ((tc : ℕ) : ZMod 2) + ((tc : ℕ) : ZMod 2) := by
              have h' := congrArg (fun t : ℕ => (t : ZMod 2)) htc
              push_cast at h'
              exact h'
            rw [hrn2, hc2'] at h
            exact (by decide : ∀ A B Q U T : ZMod 2,
              A * (U + U) - (B - Q * A) * (T + T) = 1 → False)
              ((a : ℤ) : ZMod 2) ((b : ℤ) : ZMod 2) ((q : ℤ) : ZMod 2)
              ((u : ℕ) : ZMod 2) ((tc : ℕ) : ZMod 2) h
          · exact hro
        obtain ⟨m0, hm0⟩ := (ih rn hrnc hrnpos (b - q * a) (-a) (-(c : ℤ)) hdet4).1 hro
        obtain ⟨tu, htu⟩ := hro
        have hrr : ((rn : ℕ) : ZMod 4) = 2 * ((tu : ℕ) : ZMod 4) + 1 := by
          have h := congrArg (fun t : ℕ => (t : ZMod 4)) htu
          push_cast at h
          linear_combination h
        have hdvd : (4 : ℤ) ∣ ((a + d) * c - b * d * ((c : ℤ) ^ 2 - 1) + 3 * d - 3 * c * d
            - ((b - q * a + -(c : ℤ)) * rn - (-a) * (-(c : ℤ)) * ((rn : ℤ) ^ 2 - 1)
               - 3 * rn + 3) - 3 - q) := by
          have h0 : (((a + d) * c - b * d * ((c : ℤ) ^ 2 - 1) + 3 * d - 3 * c * d
              - ((b - q * a + -(c : ℤ)) * rn - (-a) * (-(c : ℤ)) * ((rn : ℤ) ^ 2 - 1)
                 - 3 * rn + 3) - 3 - q : ℤ) : ZMod 4) = 0 := by
            have hd3c : ((d : ℤ) : ZMod 4)
                = (c : ZMod 4) * ((q : ℤ) : ZMod 4) + (rn : ZMod 4) := by
              have h := congrArg (fun t : ℤ => (t : ZMod 4)) hd3
              push_cast at h ⊢
              exact h
            have hdetc : ((a : ℤ) : ZMod 4) * (2 * ((tu : ℕ) : ZMod 4) + 1)
                - (((b : ℤ) : ZMod 4) - ((q : ℤ) : ZMod 4) * ((a : ℤ) : ZMod 4))
                  * (2 * ((tc : ℕ) : ZMod 4)) = 1 := by
              have h := congrArg (fun t : ℤ => (t : ZMod 4)) hdet3
              push_cast at h
              rw [hcc, hrr] at h
              linear_combination h
            push_cast
            rw [hd3c, hcc, hrr]
            linear_combination closure4_eo ((a : ℤ) : ZMod 4) ((b : ℤ) : ZMod 4)
              ((tc : ℕ) : ZMod 4) ((q : ℤ) : ZMod 4) ((tu : ℕ) : ZMod 4) hdetc
          have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1 h0
          exact_mod_cast h1
        obtain ⟨j, hj⟩ := hdvd
        refine ⟨m0 - j, ?_⟩
        rw [hkey, hm0]
        have hjq := congrArg (fun t : ℤ => (t : ℚ)) hj
        push_cast at hjq ⊢
        linear_combination (-1 : ℚ) * hjq

end PhiDescent

theorem twelve_mul_etaPhase_eq_gcd_mul (ℓ c' : ℕ) (hℓ : 1 ≤ ℓ) (a d : ℤ)
    (h1 : a * d ≡ 1 [ZMOD (ℓ * c' : ℕ)]) :
    ∃ z : ℤ, 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ))
        + dedekindSum d c' - dedekindSum d (ℓ * c'))
      = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z := by
  rcases Nat.eq_zero_or_pos c' with rfl | hc'pos
  · refine ⟨0, ?_⟩
    rw [Nat.mul_zero, dedekindSum_zero_right]
    push_cast
    norm_num
  · have hcpos : 0 < ℓ * c' := Nat.mul_pos hℓ hc'pos
    have hcq : ((ℓ * c' : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hcpos.ne'
    have hlq : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega : ℓ ≠ 0)
    have hc'q : (c' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hc'pos.ne'

    obtain ⟨e, he⟩ := Int.modEq_iff_dvd.1 h1
    set b : ℤ := -e with hb
    have hdet : a * d - b * (ℓ * c' : ℕ) = 1 := by
      rw [hb]
      linear_combination -he
    have hdet' : a * d - (b * ℓ) * (c' : ℕ) = 1 := by
      rw [← hdet]
      push_cast
      ring

    obtain ⟨m3, hm3⟩ := radPhi_modThree (ℓ * c') hcpos a b d hdet
    obtain ⟨m3', hm3'⟩ := radPhi_modThree c' hc'pos a (b * ℓ) d hdet'
    set P3 : ℤ := (a + d) * (ℓ * c' : ℕ) - b * d * (((ℓ * c' : ℕ) : ℤ) ^ 2 - 1) with hP3
    set P3' : ℤ := (a + d) * (c' : ℕ) - (b * ℓ) * d * (((c' : ℕ) : ℤ) ^ 2 - 1) with hP3'
    set X : ℤ := (P3 + 3 * m3) - (P3' + 3 * m3') with hX

    have hbridge : 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ))
        + dedekindSum d c' - dedekindSum d (ℓ * c'))
        = (((a + d : ℤ) : ℚ) / (ℓ * c' : ℕ) - 12 * dedekindSum d (ℓ * c'))
          - (((a + d : ℤ) : ℚ) / (c' : ℕ) - 12 * dedekindSum d c') := by
      field_simp
      push_cast
      ring
    have hXq : 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ))
        + dedekindSum d c' - dedekindSum d (ℓ * c')) = (X : ℚ) := by
      rw [hbridge, hm3, hm3', hX]
      push_cast
      ring

    set k : ℕ := Nat.gcd (ℓ - 1) 12 with hk
    have hkl : (k : ℤ) ∣ ((ℓ : ℤ) - 1) := by
      have h' : (k : ℤ) ∣ ((ℓ - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
      rwa [Nat.cast_sub hℓ, Nat.cast_one] at h'
    have hk12 : (k : ℤ) ∣ 12 := by
      exact_mod_cast Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right (ℓ - 1) 12)

    have hX3 : X = ((ℓ : ℤ) - 1) * ((a + d) * c' - b * d * ((ℓ : ℤ) * (c' : ℤ) ^ 2 + 1))
        + 3 * (m3 - m3') := by
      rw [hX, hP3, hP3']
      push_cast
      ring
    have hdvd4X : (k : ℤ) ∣ 4 * X := by
      rw [hX3]
      have : (4 : ℤ) * (((ℓ : ℤ) - 1) * ((a + d) * c' - b * d * ((ℓ : ℤ) * (c' : ℤ) ^ 2 + 1))
          + 3 * (m3 - m3'))
          = ((ℓ : ℤ) - 1) * (4 * ((a + d) * c' - b * d * ((ℓ : ℤ) * (c' : ℤ) ^ 2 + 1)))
            + 12 * (m3 - m3') := by ring
      rw [this]
      exact dvd_add (Dvd.dvd.mul_right hkl _) (Dvd.dvd.mul_right hk12 _)

    have hdvd3X : (k : ℤ) ∣ 3 * X := by
      rcases Nat.even_or_odd ℓ with hle | hlo
      ·
        have hlodd : Odd (ℓ - 1) := by
          obtain ⟨t, ht⟩ := hle
          exact ⟨t - 1, by omega⟩
        have hk2 : ¬ 2 ∣ k := by
          intro h2
          have : 2 ∣ ℓ - 1 := h2.trans (Nat.gcd_dvd_left _ _)
          rw [Nat.odd_iff] at hlodd
          omega
        have hco2 : Nat.Coprime k 2 := by
          rcases (Nat.dvd_prime Nat.prime_two).1 (Nat.gcd_dvd_right k 2) with h | h
          · exact h
          · exact absurd (h ▸ Nat.gcd_dvd_left k 2) hk2
        have hco4 : Nat.Coprime k 4 := by
          have h22 : Nat.Coprime k (2 ^ 2) := Nat.Coprime.pow_right 2 hco2
          norm_num at h22
          exact h22
        have hk3 : (k : ℤ) ∣ 3 := by
          have : k ∣ 3 := (Nat.Coprime.dvd_of_dvd_mul_right hco4)
            (by rw [show (3 * 4 : ℕ) = 12 from rfl]; exact Nat.gcd_dvd_right (ℓ - 1) 12)
          exact_mod_cast Int.natCast_dvd_natCast.2 this
        exact Dvd.dvd.mul_right hk3 X
      ·
        rcases Nat.even_or_odd c' with hc'e | hc'o
        ·
          have hce : Even (ℓ * c') := hc'e.mul_left ℓ
          obtain ⟨m4, hm4⟩ := (radPhi_modFour (ℓ * c') hcpos a b d hdet).2 hce
          obtain ⟨m4', hm4'⟩ := (radPhi_modFour c' hc'pos a (b * ℓ) d hdet').2 hc'e
          have he1 : P3 + 3 * m3
              = (a + d) * (ℓ * c' : ℕ) - b * d * (((ℓ * c' : ℕ) : ℤ) ^ 2 - 1)
                + 3 * d - 3 * (ℓ * c' : ℕ) * d + 4 * m4 := by
            exact Int.cast_injective (hm3.symm.trans hm4)
          have he2 : P3' + 3 * m3'
              = (a + d) * (c' : ℕ) - (b * ℓ) * d * (((c' : ℕ) : ℤ) ^ 2 - 1)
                + 3 * d - 3 * (c' : ℕ) * d + 4 * m4' := by
            exact Int.cast_injective (hm3'.symm.trans hm4')
          have hX4 : X = ((ℓ : ℤ) - 1) * ((a + d) * c'
              - b * d * ((ℓ : ℤ) * (c' : ℤ) ^ 2 + 1) - 3 * d * c') + 4 * (m4 - m4') := by
            rw [hX, he1, he2]
            push_cast
            ring
          rw [hX4]
          have : (3 : ℤ) * (((ℓ : ℤ) - 1) * ((a + d) * c'
              - b * d * ((ℓ : ℤ) * (c' : ℤ) ^ 2 + 1) - 3 * d * c') + 4 * (m4 - m4'))
              = ((ℓ : ℤ) - 1) * (3 * ((a + d) * c'
                - b * d * ((ℓ : ℤ) * (c' : ℤ) ^ 2 + 1) - 3 * d * c')) + 12 * (m4 - m4') := by
            ring
          rw [this]
          exact dvd_add (Dvd.dvd.mul_right hkl _) (Dvd.dvd.mul_right hk12 _)
        ·
          have hco : Odd (ℓ * c') := hlo.mul hc'o
          obtain ⟨m4, hm4⟩ := (radPhi_modFour (ℓ * c') hcpos a b d hdet).1 hco
          obtain ⟨m4', hm4'⟩ := (radPhi_modFour c' hc'pos a (b * ℓ) d hdet').1 hc'o
          have he1 : P3 + 3 * m3
              = (a + d) * (ℓ * c' : ℕ) - b * d * (((ℓ * c' : ℕ) : ℤ) ^ 2 - 1)
                - 3 * (ℓ * c' : ℕ) + 3 + 4 * m4 := by
            exact Int.cast_injective (hm3.symm.trans hm4)
          have he2 : P3' + 3 * m3'
              = (a + d) * (c' : ℕ) - (b * ℓ) * d * (((c' : ℕ) : ℤ) ^ 2 - 1)
                - 3 * (c' : ℕ) + 3 + 4 * m4' := by
            exact Int.cast_injective (hm3'.symm.trans hm4')
          have hX4 : X = ((ℓ : ℤ) - 1) * ((a + d) * c'
              - b * d * ((ℓ : ℤ) * (c' : ℤ) ^ 2 + 1) - 3 * c') + 4 * (m4 - m4') := by
            rw [hX, he1, he2]
            push_cast
            ring
          rw [hX4]
          have : (3 : ℤ) * (((ℓ : ℤ) - 1) * ((a + d) * c'
              - b * d * ((ℓ : ℤ) * (c' : ℤ) ^ 2 + 1) - 3 * c') + 4 * (m4 - m4'))
              = ((ℓ : ℤ) - 1) * (3 * ((a + d) * c'
                - b * d * ((ℓ : ℤ) * (c' : ℤ) ^ 2 + 1) - 3 * c')) + 12 * (m4 - m4') := by
            ring
          rw [this]
          exact dvd_add (Dvd.dvd.mul_right hkl _) (Dvd.dvd.mul_right hk12 _)

    have hdvdX : (k : ℤ) ∣ X := by
      have h4 : (4 : ℤ) * X - 3 * X = X := by ring
      rw [← h4]
      exact dvd_sub hdvd4X hdvd3X
    obtain ⟨z, hz⟩ := hdvdX
    refine ⟨z, ?_⟩
    rw [hXq, hz]
    push_cast
    ring

theorem twelve_mul_etaPhase_generator (ℓ b bs : ℕ) (hℓ : 1 ≤ ℓ) (h : ℓ ∣ b * bs + 1) :
    ∃ z : ℤ, 12 * ((((b : ℤ) - (bs : ℤ) : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((b * bs + 1 : ℕ) : ℚ))
        + dedekindSum b ((b * bs + 1) / ℓ) - dedekindSum b (b * bs + 1))
      = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z := by
  have hc : ℓ * ((b * bs + 1) / ℓ) = b * bs + 1 := Nat.mul_div_cancel' h
  have hmod : (-(bs : ℤ)) * (b : ℤ) ≡ 1 [ZMOD ((ℓ * ((b * bs + 1) / ℓ) : ℕ) : ℤ)] := by
    rw [hc]
    refine Int.modEq_iff_dvd.2 ⟨1, ?_⟩
    push_cast
    ring
  obtain ⟨z, hz⟩ := twelve_mul_etaPhase_eq_gcd_mul ℓ ((b * bs + 1) / ℓ) hℓ (-(bs : ℤ)) (b : ℤ) hmod
  rw [hc] at hz
  refine ⟨z, ?_⟩
  have hcast : ((-(bs : ℤ) + (b : ℤ) : ℤ) : ℚ) = (((b : ℤ) - (bs : ℤ) : ℤ) : ℚ) := by
    push_cast
    ring
  rw [hcast] at hz
  exact hz

theorem etaPhase_witness_eleven (j : ℕ) :
    12 * ((((4 * j + 4 : ℕ) + 3 : ℤ) : ℚ) * (1 - ((12 * j + 11 : ℕ) : ℚ))
          / (12 * ((12 * j + 11 : ℕ) : ℚ))
        + dedekindSum 3 1 - dedekindSum 3 (12 * j + 11))
      = ((Nat.gcd ((12 * j + 11) - 1) 12 : ℕ) : ℚ) * (-(4 * (j : ℤ) + 4)) ∧
    Nat.Coprime (Int.natAbs (-(4 * (j : ℤ) + 4)))
      (((12 * j + 11) - 1) / Nat.gcd ((12 * j + 11) - 1) 12) := by
  have hgcd : Nat.gcd ((12 * j + 11) - 1) 12 = 2 := by
    rw [show (12 * j + 11) - 1 = 10 + j * 12 from by omega, Nat.gcd_add_mul_right_left]
    decide
  have hL : ((12 * j + 11 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  constructor
  ·
    have hco : Nat.Coprime 3 (12 * j + 11) := by
      rw [Nat.coprime_comm]
      unfold Nat.Coprime
      rw [show 12 * j + 11 = 2 + (4 * j + 3) * 3 from by ring, Nat.gcd_add_mul_right_left]
      decide
    have hrec := dedekindSum_add_dedekindSum 3 (12 * j + 11) (by norm_num) (by omega) hco
    have hs23 : dedekindSum 2 3 = -(1 / 18 : ℚ) := by
      rw [show (2 : ℤ) = -1 + 1 * ((3 : ℕ) : ℤ) from by norm_num, dedekindSum_add_mul,
        show (-1 : ℤ) = -(1 : ℤ) from rfl, dedekindSum_neg, dedekindSum_one_left]
      norm_num
    have hl3 : dedekindSum ((12 * j + 11 : ℕ) : ℤ) 3 = dedekindSum 2 3 := by
      rw [show ((12 * j + 11 : ℕ) : ℤ) = 2 + ((4 * j + 3 : ℕ) : ℤ) * ((3 : ℕ) : ℤ) from by
        push_cast; ring, dedekindSum_add_mul]
    have hs3l : dedekindSum 3 (12 * j + 11)
        = ((3 : ℚ) / (12 * j + 11 : ℕ) + ((12 * j + 11 : ℕ) : ℚ) / 3
            + 1 / (3 * ((12 * j + 11 : ℕ) : ℚ))) / 12 - 1 / 4 + 1 / 18 := by
      have h := hrec
      rw [hl3, hs23] at h
      linarith [h]
    rw [hgcd, dedekindSum_one_right, hs3l]
    push_cast
    field_simp
    ring
  ·
    rw [hgcd, show ((12 * j + 11) - 1) / 2 = 6 * j + 5 from by omega,
      show (-(4 * (j : ℤ) + 4)) = -((4 * j + 4 : ℕ) : ℤ) from by push_cast; ring,
      Int.natAbs_neg, Int.natAbs_natCast]
    have ha := Nat.gcd_dvd_left (4 * j + 4) (6 * j + 5)
    have hb := Nat.gcd_dvd_right (4 * j + 4) (6 * j + 5)
    have h2 : Nat.gcd (4 * j + 4) (6 * j + 5) ∣ 2 := by
      have h3 := Nat.dvd_sub (Dvd.dvd.mul_left ha 3) (Dvd.dvd.mul_left hb 2)
      rwa [show 3 * (4 * j + 4) - 2 * (6 * j + 5) = 2 from by omega] at h3
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · exfalso
      have : 2 ∣ 6 * j + 5 := h ▸ hb
      omega

theorem etaPhase_witness_five (j : ℕ) :
    12 * ((((4 * j + 2 : ℕ) + 3 : ℤ) : ℚ) * (1 - ((12 * j + 5 : ℕ) : ℚ))
          / (12 * ((12 * j + 5 : ℕ) : ℚ))
        + dedekindSum 3 1 - dedekindSum 3 (12 * j + 5))
      = ((Nat.gcd ((12 * j + 5) - 1) 12 : ℕ) : ℚ) * (-(2 * (j : ℤ) + 1)) ∧
    Nat.Coprime (Int.natAbs (-(2 * (j : ℤ) + 1)))
      (((12 * j + 5) - 1) / Nat.gcd ((12 * j + 5) - 1) 12) := by
  have hgcd : Nat.gcd ((12 * j + 5) - 1) 12 = 4 := by
    rw [show (12 * j + 5) - 1 = 4 + j * 12 from by omega, Nat.gcd_add_mul_right_left]
    decide
  have hL : ((12 * j + 5 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  constructor
  · have hco : Nat.Coprime 3 (12 * j + 5) := by
      rw [Nat.coprime_comm]
      unfold Nat.Coprime
      rw [show 12 * j + 5 = 2 + (4 * j + 1) * 3 from by ring, Nat.gcd_add_mul_right_left]
      decide
    have hrec := dedekindSum_add_dedekindSum 3 (12 * j + 5) (by norm_num) (by omega) hco
    have hs23 : dedekindSum 2 3 = -(1 / 18 : ℚ) := by
      rw [show (2 : ℤ) = -1 + 1 * ((3 : ℕ) : ℤ) from by norm_num, dedekindSum_add_mul,
        show (-1 : ℤ) = -(1 : ℤ) from rfl, dedekindSum_neg, dedekindSum_one_left]
      norm_num
    have hl3 : dedekindSum ((12 * j + 5 : ℕ) : ℤ) 3 = dedekindSum 2 3 := by
      rw [show ((12 * j + 5 : ℕ) : ℤ) = 2 + ((4 * j + 1 : ℕ) : ℤ) * ((3 : ℕ) : ℤ) from by
        push_cast; ring, dedekindSum_add_mul]
    have hs3l : dedekindSum 3 (12 * j + 5)
        = ((3 : ℚ) / (12 * j + 5 : ℕ) + ((12 * j + 5 : ℕ) : ℚ) / 3
            + 1 / (3 * ((12 * j + 5 : ℕ) : ℚ))) / 12 - 1 / 4 + 1 / 18 := by
      have h := hrec
      rw [hl3, hs23] at h
      linarith [h]
    rw [hgcd, dedekindSum_one_right, hs3l]
    push_cast
    field_simp
    ring
  ·
    rw [hgcd, show ((12 * j + 5) - 1) / 4 = 3 * j + 1 from by omega,
      show (-(2 * (j : ℤ) + 1)) = -((2 * j + 1 : ℕ) : ℤ) from by push_cast; ring,
      Int.natAbs_neg, Int.natAbs_natCast]
    have ha := Nat.gcd_dvd_left (2 * j + 1) (3 * j + 1)
    have hb := Nat.gcd_dvd_right (2 * j + 1) (3 * j + 1)
    have h1 : Nat.gcd (2 * j + 1) (3 * j + 1) ∣ 1 := by
      have h3 := Nat.dvd_sub (Dvd.dvd.mul_left ha 3) (Dvd.dvd.mul_left hb 2)
      rwa [show 3 * (2 * j + 1) - 2 * (3 * j + 1) = 1 from by omega] at h3
    exact Nat.dvd_one.mp h1

theorem etaPhase_witness_seven (j : ℕ) :
    12 * ((((3 * j + 2 : ℕ) + 4 : ℤ) : ℚ) * (1 - ((12 * j + 7 : ℕ) : ℚ))
          / (12 * ((12 * j + 7 : ℕ) : ℚ))
        + dedekindSum 4 1 - dedekindSum 4 (12 * j + 7))
      = ((Nat.gcd ((12 * j + 7) - 1) 12 : ℕ) : ℚ) * (-((j : ℤ) + 1)) ∧
    Nat.Coprime (Int.natAbs (-((j : ℤ) + 1)))
      (((12 * j + 7) - 1) / Nat.gcd ((12 * j + 7) - 1) 12) := by
  have hgcd : Nat.gcd ((12 * j + 7) - 1) 12 = 6 := by
    rw [show (12 * j + 7) - 1 = 6 + j * 12 from by omega, Nat.gcd_add_mul_right_left]
    decide
  have hL : ((12 * j + 7 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  constructor
  · have hco : Nat.Coprime 4 (12 * j + 7) := by
      rw [Nat.coprime_comm]
      unfold Nat.Coprime
      rw [show 12 * j + 7 = 3 + (3 * j + 1) * 4 from by ring, Nat.gcd_add_mul_right_left]
      decide
    have hrec := dedekindSum_add_dedekindSum 4 (12 * j + 7) (by norm_num) (by omega) hco
    have hs34 : dedekindSum 3 4 = -(1 / 8 : ℚ) := by
      rw [show (3 : ℤ) = -1 + 1 * ((4 : ℕ) : ℤ) from by norm_num, dedekindSum_add_mul,
        show (-1 : ℤ) = -(1 : ℤ) from rfl, dedekindSum_neg, dedekindSum_one_left]
      norm_num
    have hl4 : dedekindSum ((12 * j + 7 : ℕ) : ℤ) 4 = dedekindSum 3 4 := by
      rw [show ((12 * j + 7 : ℕ) : ℤ) = 3 + ((3 * j + 1 : ℕ) : ℤ) * ((4 : ℕ) : ℤ) from by
        push_cast; ring, dedekindSum_add_mul]
    have hs4l : dedekindSum 4 (12 * j + 7)
        = ((4 : ℚ) / (12 * j + 7 : ℕ) + ((12 * j + 7 : ℕ) : ℚ) / 4
            + 1 / (4 * ((12 * j + 7 : ℕ) : ℚ))) / 12 - 1 / 4 + 1 / 8 := by
      have h := hrec
      rw [hl4, hs34] at h
      linarith [h]
    rw [hgcd, dedekindSum_one_right, hs4l]
    push_cast
    field_simp
    ring
  ·
    rw [hgcd, show ((12 * j + 7) - 1) / 6 = 2 * j + 1 from by omega,
      show (-((j : ℤ) + 1)) = -((j + 1 : ℕ) : ℤ) from by push_cast; ring,
      Int.natAbs_neg, Int.natAbs_natCast]
    have ha := Nat.gcd_dvd_left (j + 1) (2 * j + 1)
    have hb := Nat.gcd_dvd_right (j + 1) (2 * j + 1)
    have h1 : Nat.gcd (j + 1) (2 * j + 1) ∣ 1 := by
      have h3 := Nat.dvd_sub (Dvd.dvd.mul_left ha 2) hb
      rwa [show 2 * (j + 1) - (2 * j + 1) = 1 from by omega] at h3
    exact Nat.dvd_one.mp h1

theorem etaPhase_witness_thirtySeven :
    12 * (((15 + 5 : ℤ) : ℚ) * (1 - ((37 : ℕ) : ℚ)) / (12 * ((37 : ℕ) : ℚ))
        + dedekindSum 5 1 - dedekindSum 5 37)
      = ((Nat.gcd (37 - 1) 12 : ℕ) : ℚ) * (-2) ∧
    Nat.Coprime (Int.natAbs (-2)) ((37 - 1) / Nat.gcd (37 - 1) 12) := by
  constructor
  ·
    have hs12 : dedekindSum 1 2 = 0 := by
      rw [dedekindSum_one_left]
      norm_num
    have hs52 : dedekindSum 5 2 = 0 := by
      rw [show (5 : ℤ) = 1 + 2 * ((2 : ℕ) : ℤ) from by norm_num, dedekindSum_add_mul]
      exact hs12
    have hrec25 := dedekindSum_add_dedekindSum 2 5 (by norm_num) (by norm_num) (by decide)
    have hs25 : dedekindSum 2 5 = 0 := by
      have h5 : dedekindSum ((5 : ℕ) : ℤ) 2 = 0 := by
        rw [show ((5 : ℕ) : ℤ) = (5 : ℤ) from by norm_num]
        exact hs52
      rw [h5] at hrec25
      have : dedekindSum 2 5 + 0 = ((2 : ℚ) / 5 + 5 / 2 + 1 / (2 * 5)) / 12 - 1 / 4 := by
        exact_mod_cast hrec25
      rw [add_zero] at this
      rw [this]
      norm_num
    have hs375 : dedekindSum ((37 : ℕ) : ℤ) 5 = 0 := by
      rw [show ((37 : ℕ) : ℤ) = 2 + 7 * ((5 : ℕ) : ℤ) from by norm_num, dedekindSum_add_mul]
      exact hs25
    have hrec537 := dedekindSum_add_dedekindSum 5 37 (by norm_num) (by norm_num) (by decide)
    have hs537 : dedekindSum 5 37 = 14 / 37 := by
      rw [hs375] at hrec537
      have : dedekindSum 5 37 + 0 = ((5 : ℚ) / 37 + 37 / 5 + 1 / (5 * 37)) / 12 - 1 / 4 := by
        exact_mod_cast hrec537
      rw [add_zero] at this
      rw [this]
      norm_num
    rw [dedekindSum_one_right, hs537, show Nat.gcd (37 - 1) 12 = 12 from by decide]
    norm_num
  · decide

theorem radPhi_step (c r : ℕ) (hc : 0 < c) (hr : 0 < r) (a b d q : ℤ)
    (hrd : (r : ℤ) = q * c - d) (hdet : a * d - b * c = 1) :
    ((a + d : ℤ) : ℚ) / c - 12 * dedekindSum d c
      = ((q * a - b + c : ℤ) : ℚ) / r - 12 * dedekindSum c r + q - 3 := by
  have hdet1 : (q * a - b) * c - a * r = 1 := by
    rw [hrd]
    linear_combination hdet
  have hcor : Nat.Coprime r c := by
    have hgd : (Int.gcd (r : ℤ) c : ℤ) ∣ (q * a - b) * c - a * r :=
      dvd_sub (Dvd.dvd.mul_left (Int.gcd_dvd_right (r : ℤ) c) (q * a - b))
        (Dvd.dvd.mul_left (Int.gcd_dvd_left (r : ℤ) c) a)
    rw [hdet1] at hgd
    have hg1 : Int.gcd (r : ℤ) c ∣ 1 := by exact_mod_cast hgd
    have hg2 : Int.gcd (r : ℤ) c = 1 := Nat.dvd_one.mp hg1
    rwa [Int.gcd_natCast_natCast] at hg2
  have hd : d = -(r : ℤ) + q * c := by linear_combination hrd
  have hper : dedekindSum d c = -dedekindSum r c := by
    rw [hd, dedekindSum_add_mul, dedekindSum_neg]
  have hrec := dedekindSum_add_dedekindSum r c hr hc hcor
  have hrec12 : 12 * (r : ℚ) * c * (dedekindSum r c + dedekindSum c r)
      = (r : ℚ) ^ 2 + (c : ℚ) ^ 2 + 1 - 3 * r * c := by
    rw [hrec]
    field_simp
    ring
  have hdetq : ((q : ℚ) * a - b) * c - a * r = 1 := by exact_mod_cast hdet1
  rw [hper]
  push_cast
  rw [hd]
  push_cast
  field_simp
  linear_combination hrec12 - hdetq

theorem radPhi_base (a d : ℤ) :
    ((a + d : ℤ) : ℚ) / ((1 : ℕ) : ℚ) - 12 * dedekindSum d 1 = (a : ℚ) + d := by
  rw [dedekindSum_one_right]
  push_cast
  ring

end DedekindSumRows

theorem solution (ℓ c' : ℕ) (hℓ : 1 ≤ ℓ) (a d : ℤ) (h1 : Int.ModEq ((ℓ * c' : ℕ) : ℤ) (a * d) 1) : ∃ z : ℤ, 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ)) + dedekindSum d c' - dedekindSum d (ℓ * c')) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z :=
  DedekindSumRows.twelve_mul_etaPhase_eq_gcd_mul ℓ c' hℓ a d h1

end S_rademacher_phi_level_congruence
end P2MW
export P2MW.S_rademacher_phi_level_congruence (solution)
