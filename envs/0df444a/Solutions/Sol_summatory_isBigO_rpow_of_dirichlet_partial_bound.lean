-- Prove2me | solution 1 for summatory_isBigO_rpow_of_dirichlet_partial_bound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T15:21:52.318684+00:00
-- url     : https://prove2.me/submissions/06a31201-4e13-408a-8607-3104b8ff2418

import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
open Filter Asymptotics

/-- Discrete Abel summation: multiplying a sequence with bounded partial sums by
nonnegative increasing weights costs at most twice the final weight. -/
theorem norm_sum_range_smul_le_of_bounded_partials
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℕ → E) (w : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hw : Monotone w) (hw0 : 0 ≤ w 0)
    (hbound : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, a i‖ ≤ C) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, w i • a i‖ ≤ 2 * C * w (n - 1) := by
  have hwpos (i : ℕ) : 0 ≤ w i := hw0.trans (hw (Nat.zero_le i))
  have hdiff (i : ℕ) : 0 ≤ w (i + 1) - w i := sub_nonneg.mpr (hw (Nat.le_succ i))
  rw [Finset.sum_range_by_parts]
  calc
    _ ≤ ‖w (n - 1) • ∑ i ∈ Finset.range n, a i‖ +
        ‖∑ i ∈ Finset.range (n - 1),
          (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), a j‖ := norm_sub_le _ _
    _ ≤ w (n - 1) * C +
        ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) * C := by
      apply add_le_add
      · rw [norm_smul, Real.norm_of_nonneg (hwpos _)]
        exact mul_le_mul_of_nonneg_left (hbound n) (hwpos _)
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => by
          rw [norm_smul, Real.norm_of_nonneg (hdiff i)]
          exact mul_le_mul_of_nonneg_left (hbound (i + 1)) (hdiff i)))
    _ = w (n - 1) * C + (w (n - 1) - w 0) * C := by
      rw [← Finset.sum_mul, Finset.sum_range_sub]
    _ ≤ 2 * C * w (n - 1) := by nlinarith

/-- A uniform bound for finite Dirichlet sums on a positive real line implies
the corresponding power bound for the ordinary summatory function. -/
theorem norm_sum_Icc_le_of_dirichlet_partial_bound
    (a : ℕ → ℂ) (σ C : ℝ) (hσ : 0 ≤ σ) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ,
      ‖∑ i ∈ Finset.Icc 1 n, a i / (i : ℂ) ^ (σ : ℂ)‖ ≤ C) (n : ℕ) :
    ‖∑ i ∈ Finset.Icc 1 n, a i‖ ≤ 2 * C * (n : ℝ) ^ σ := by
  let v (i : ℕ) : ℂ := a (i + 1) / ((i + 1 : ℕ) : ℂ) ^ (σ : ℂ)
  let w (i : ℕ) : ℝ := ((i + 1 : ℕ) : ℝ) ^ σ
  have hsum (f : ℕ → ℂ) (k : ℕ) :
      ∑ i ∈ Finset.range k, f (i + 1) = ∑ i ∈ Finset.Icc 1 k, f i := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add']
    simp only [zero_add, Finset.Ico_add_one_right_eq_Icc]
  have hv (k : ℕ) : ‖∑ i ∈ Finset.range k, v i‖ ≤ C := by
    change ‖∑ i ∈ Finset.range k,
      (fun j : ℕ => a j / (j : ℂ) ^ (σ : ℂ)) (i + 1)‖ ≤ C
    rw [hsum (fun j : ℕ => a j / (j : ℂ) ^ (σ : ℂ)) k]
    exact hbound k
  have hw : Monotone w := by
    intro i j hij
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1) hσ
  have hwv (i : ℕ) : w i • v i = a (i + 1) := by
    have hn : (Complex.ofReal (((i + 1 : ℕ) : ℝ) ^ σ)) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos
        (by positivity : 0 < ((i + 1 : ℕ) : ℝ)) σ))
    dsimp [w, v]
    rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_natCast] at hn ⊢
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ hn
  have h := norm_sum_range_smul_le_of_bounded_partials v w C hC hw (by
    dsimp [w]
    positivity) hv n
  simp_rw [hwv, hsum] at h
  by_cases hn : n = 0
  · subst n
    simpa using (mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg (by positivity) σ))
  · simpa only [w, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] using h

theorem solution
    (a : ℕ → ℂ) (σ : ℝ) (hσ : 0 ≤ σ)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖∑ i ∈ Finset.Icc 1 n, a i / (i : ℂ) ^ (σ : ℂ)‖ ≤ C) :
    (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, a i) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ σ) := by
  obtain ⟨C, hC, hbound⟩ := hbound
  apply IsBigO.of_bound (2 * C)
  exact Filter.Eventually.of_forall (fun n => by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)] using
      norm_sum_Icc_le_of_dirichlet_partial_bound a σ C hσ hC hbound n)
