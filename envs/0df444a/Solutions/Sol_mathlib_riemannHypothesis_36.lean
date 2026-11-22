-- Prove2me | solution 36 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:48.920714+00:00
-- url     : https://prove2.me/submissions/25e75c78-7c02-4e1e-ba18-26d3d89fc848
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_half_lt
import Theorems.Thm_ordered_dirichlet_convergence_implies_little_o_partial_sums
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound

-- Step 1: `moebius_dirichlet_partialSum_tendsto_of_half_lt` implies `moebius_summatory_rpow_bound` (accepted reduction of `moebius_summatory_rpow_bound`).
section

theorem moebius_summatory_rpow_bound :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by
  intro ε hε
  let σ : ℝ := 1 / 2 + ε
  have hσ : 1 / 2 < σ := by dsimp [σ]; linarith
  obtain ⟨L, hL⟩ := moebius_dirichlet_partialSum_tendsto_of_half_lt σ hσ
  apply (ordered_dirichlet_convergence_implies_little_o_partial_sums
    (fun n => (ArithmeticFunction.moebius n : ℂ)) (σ := σ) (by linarith)
    (L := (L : ℂ)) ?_).isBigO
  have hterm (n : ℕ) :
      (((ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) =
        (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ (σ : ℂ) := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_cpow (Nat.cast_nonneg n), div_eq_mul_inv]
    push_cast
    rfl
  simpa only [Function.comp_def, Complex.ofReal_sum, hterm] using
    (Complex.continuous_ofReal.tendsto L).comp hL

end

-- Step 2: `moebius_summatory_rpow_bound` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  by
  intro s hz htriv hone
  have key : ∀ ε : ℝ, 0 < ε → 1 / 2 - ε ≤ s.re ∧ s.re ≤ 1 / 2 + ε := by
    intro ε hε
    have h := nontrivial_zero_strip_of_moebius_summatory_power_bound
      (r := 1 / 2 + ε) (by linarith) (moebius_summatory_rpow_bound ε hε) hz htriv hone
    constructor <;> linarith [h.1, h.2]
  have hle : s.re ≤ 1 / 2 := by
    by_contra hlt
    push_neg at hlt
    have := (key ((s.re - 1 / 2) / 2) (by linarith)).2
    linarith
  have hge : 1 / 2 ≤ s.re := by
    by_contra hlt
    push_neg at hlt
    have := (key ((1 / 2 - s.re) / 2) (by linarith)).1
    linarith
  exact le_antisymm hle hge

end
