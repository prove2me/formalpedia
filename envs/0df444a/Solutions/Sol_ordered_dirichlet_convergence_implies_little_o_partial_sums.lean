-- Prove2me | solution 1 for ordered_dirichlet_convergence_implies_little_o_partial_sums
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:09:01.62825+00:00
-- url     : https://prove2.me/submissions/27a7c639-d92b-47a1-b207-453a798ebd96

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open Finset Filter Complex Asymptotics
open scoped Topology

namespace DirichletKronecker6fec

theorem norm_sum_range_smul_le_of_monotone
    (a : ℕ → ℂ) (g : ℕ → ℝ) (hg : Monotone g) (hg0 : 0 ≤ g 0)
    (B : ℝ) (hB : ∀ n : ℕ, ‖∑ k ∈ range n, a k‖ ≤ B) (N : ℕ) :
    ‖∑ k ∈ range N, g k • a k‖ ≤ 2 * B * g (N - 1) := by
  have hB0 : 0 ≤ B := by simpa using hB 0
  have hgpos (n : ℕ) : 0 ≤ g n := hg0.trans (hg (Nat.zero_le n))
  have hdiff (n : ℕ) : 0 ≤ g (n + 1) - g n := sub_nonneg.mpr (hg (Nat.le_succ n))
  rw [sum_range_by_parts]
  calc
    ‖g (N - 1) • (∑ k ∈ range N, a k) -
        ∑ k ∈ range (N - 1), (g (k + 1) - g k) • (∑ j ∈ range (k + 1), a j)‖
        ≤ ‖g (N - 1) • (∑ k ∈ range N, a k)‖ +
          ‖∑ k ∈ range (N - 1), (g (k + 1) - g k) • (∑ j ∈ range (k + 1), a j)‖ :=
      norm_sub_le _ _
    _ ≤ g (N - 1) * B + ∑ k ∈ range (N - 1), (g (k + 1) - g k) * B := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hgpos _)]
        exact mul_le_mul_of_nonneg_left (hB N) (hgpos _)
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro k hk
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hdiff _)]
        exact mul_le_mul_of_nonneg_left (hB (k + 1)) (hdiff _)
    _ = g (N - 1) * B + (g (N - 1) - g 0) * B := by
      rw [← sum_mul, sum_range_sub]
    _ ≤ 2 * B * g (N - 1) := by
      nlinarith [mul_nonneg hg0 hB0]

private lemma sum_range_cutoff (a : ℕ → ℂ) (K N : ℕ) :
    ∑ n ∈ range N, (if K ≤ n then a n else 0) = ∑ n ∈ Ico K N, a n := by
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_range, mem_Ico, and_comm]

theorem weighted_sums_isLittleO_of_convergence
    (a : ℕ → ℂ) (g : ℕ → ℝ) (hg : Monotone g) (hg0 : 0 ≤ g 0)
    (hginfty : Tendsto g atTop atTop) {L : ℂ}
    (hlim : Tendsto (fun N : ℕ ↦ ∑ n ∈ range N, a n) atTop (𝓝 L)) :
    (fun N : ℕ ↦ ∑ n ∈ range (N + 1), g n • a n) =o[atTop] g := by
  have hgpos (N : ℕ) : 0 ≤ g N := hg0.trans (hg (Nat.zero_le N))
  have hgnorm : Tendsto (fun N : ℕ ↦ ‖g N‖) atTop atTop := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hgpos _)] using hginfty
  apply IsLittleO.of_bound
  intro c hc
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((Metric.tendsto_nhds.1 hlim) (c / 8) (by positivity))
  let b : ℕ → ℂ := fun n ↦ if K ≤ n then a n else 0
  have hbsum (N : ℕ) : ∑ n ∈ range N, b n = ∑ n ∈ Ico K N, a n :=
    sum_range_cutoff a K N
  have hb (N : ℕ) : ‖∑ n ∈ range N, b n‖ ≤ c / 4 := by
    rw [hbsum]
    by_cases hKN : K ≤ N
    · rw [sum_Ico_eq_sub _ hKN, ← dist_eq_norm]
      calc
        dist (∑ n ∈ range N, a n) (∑ n ∈ range K, a n)
            ≤ dist (∑ n ∈ range N, a n) L + dist (∑ n ∈ range K, a n) L := by
          simpa only [dist_comm L] using
            dist_triangle (∑ n ∈ range N, a n) L (∑ n ∈ range K, a n)
        _ ≤ c / 4 := by linarith [hK N hKN, hK K le_rfl]
    · rw [Ico_eq_empty_of_le (not_le.mp hKN).le, sum_empty, norm_zero]
      positivity
  have htail (N : ℕ) : ‖∑ n ∈ range (N + 1), g n • b n‖ ≤ (c / 2) * g N := by
    have h' := norm_sum_range_smul_le_of_monotone b g hg hg0 (c / 4) hb (N + 1)
    simpa only [Nat.add_sub_cancel, show 2 * (c / 4) = c / 2 by ring] using h'
  have hprefix : (fun _ : ℕ ↦ ∑ n ∈ range K, g n • a n) =o[atTop] g :=
    isLittleO_const_left.mpr (Or.inr hgnorm)
  have hsplit (N : ℕ) (hKN : K ≤ N) :
      ∑ n ∈ range (N + 1), g n • a n =
        (∑ n ∈ range K, g n • a n) + ∑ n ∈ range (N + 1), g n • b n := by
    have hweighted : ∑ n ∈ range (N + 1), g n • b n =
        ∑ n ∈ Ico K (N + 1), g n • a n := by
      simp only [b, smul_ite, smul_zero]
      exact sum_range_cutoff (fun n ↦ g n • a n) K (N + 1)
    rw [hweighted, sum_Ico_eq_sub _ (hKN.trans (Nat.le_succ N))]
    abel
  filter_upwards [hprefix.bound (show 0 < c / 2 by positivity), eventually_ge_atTop K]
    with N hN hKN
  simp only [Real.norm_eq_abs, abs_of_nonneg (hgpos N)] at hN ⊢
  rw [hsplit N hKN]
  calc
    ‖(∑ n ∈ range K, g n • a n) + ∑ n ∈ range (N + 1), g n • b n‖
        ≤ ‖∑ n ∈ range K, g n • a n‖ + ‖∑ n ∈ range (N + 1), g n • b n‖ :=
      norm_add_le _ _
    _ ≤ c / 2 * g N + c / 2 * g N := add_le_add hN (htail N)
    _ = c * g N := by ring

private theorem sum_range_succ_eq_sum_Icc {b : ℕ → ℂ} (hb : b 0 = 0) (N : ℕ) :
    ∑ k ∈ range (N + 1), b k = ∑ k ∈ Icc 1 N, b k := by
  rw [Nat.range_succ_eq_Icc_zero, ← insert_Icc_add_one_left_eq_Icc N.zero_le,
    sum_insert (by simp), hb, zero_add, zero_add]

theorem summatory_isLittleO_of_ordered_convergence (f : ℕ → ℂ)
    {σ : ℝ} (hσ : 0 < σ) {L : ℂ}
    (hlim : Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, f n / (n : ℂ) ^ (σ : ℂ))
      atTop (𝓝 L)) :
    (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, f n) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ) ^ σ) := by
  let a : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f n / (n : ℂ) ^ (σ : ℂ)
  let g : ℕ → ℝ := fun n ↦ (n : ℝ) ^ σ
  have ha0 : a 0 = 0 := by simp [a]
  have hsum (N : ℕ) :
      ∑ n ∈ range (N + 1), a n = ∑ n ∈ Icc 1 N, f n / (n : ℂ) ^ (σ : ℂ) := by
    rw [sum_range_succ_eq_sum_Icc ha0]
    apply sum_congr rfl
    intro n hn
    exact if_neg (zero_lt_one.trans_le (mem_Icc.mp hn).1).ne'
  have hlimA : Tendsto (fun N : ℕ ↦ ∑ n ∈ range N, a n) atTop (𝓝 L) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [hsum] using hlim
  have hg : Monotone g := by
    intro a b hab
    exact Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab) hσ.le
  have hg0 : 0 ≤ g 0 := Real.rpow_nonneg (Nat.cast_nonneg 0) σ
  have hginfty : Tendsto g atTop atTop :=
    (tendsto_rpow_atTop hσ).comp tendsto_natCast_atTop_atTop
  have hweight (N : ℕ) : ∑ n ∈ range (N + 1), g n • a n = ∑ n ∈ Icc 1 N, f n := by
    rw [sum_range_succ_eq_sum_Icc (by simp [ha0])]
    apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := (zero_lt_one.trans_le (mem_Icc.mp hn).1).ne'
    have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    dsimp only [g, a]
    rw [if_neg hn0, real_smul, ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast]
    field_simp [cpow_ne_zero_iff.mpr (Or.inl hnc)]
  simpa only [hweight] using weighted_sums_isLittleO_of_convergence a g hg hg0 hginfty hlimA

end DirichletKronecker6fec

theorem solution
    (f : ℕ → ℂ) {σ : ℝ} (hσ : 0 < σ) {L : ℂ}
    (hlim : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ (σ : ℂ))
      Filter.atTop (nhds L)) :
    Asymptotics.IsLittleO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n)
      (fun N : ℕ => (N : ℝ) ^ σ) :=
  DirichletKronecker6fec.summatory_isLittleO_of_ordered_convergence f hσ hlim

#print axioms solution
