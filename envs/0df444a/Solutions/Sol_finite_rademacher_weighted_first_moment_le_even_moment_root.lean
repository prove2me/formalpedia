-- Prove2me | solution 1 for finite_rademacher_weighted_first_moment_le_even_moment_root
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-25T20:46:45.055683+00:00
-- url     : https://prove2.me/submissions/22f6e35b-c747-4824-aadb-c6c32e804f24

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Classical BigOperators

theorem solution :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (F : Finset ι → ℝ), (∀ eps, 0 ≤ F eps) →
      ∀ p : ℕ, 1 ≤ p →
      (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι) * F eps)
        ≤ (∑ eps : Finset ι,
            ((1 : ℝ) / 2) ^ (Fintype.card ι) * (F eps) ^ (2 * p))
            ^ ((1 : ℝ) / (2 * p)) := by
  intro ι _ _ F hF p hp
  let w : Finset ι → ℝ := fun _ => ((1 : ℝ) / 2) ^ (Fintype.card ι)
  have hw_nonneg : ∀ eps ∈ (Finset.univ : Finset (Finset ι)), 0 ≤ w eps := by
    intro eps _heps
    dsimp [w]
    positivity
  have hw_sum : ∑ eps ∈ (Finset.univ : Finset (Finset ι)), w eps = 1 := by
    dsimp [w]
    simp [Fintype.card_finset]
  have hF_univ : ∀ eps ∈ (Finset.univ : Finset (Finset ι)), 0 ≤ F eps := by
    intro eps _heps
    exact hF eps
  have hp_real : (1 : ℝ) ≤ ((2 * p : ℕ) : ℝ) := by
    have hp_nat : 1 ≤ 2 * p := by nlinarith
    exact_mod_cast hp_nat
  have hmean :=
    Real.arith_mean_le_rpow_mean (s := (Finset.univ : Finset (Finset ι)))
      w F hw_nonneg hw_sum hF_univ (p := ((2 * p : ℕ) : ℝ)) hp_real
  have hpow : ∀ eps : Finset ι, F eps ^ ((2 : ℝ) * p) = F eps ^ (2 * p) := by
    intro eps
    have hcast : ((2 : ℝ) * p) = ((2 * p : ℕ) : ℝ) := by norm_num
    rw [hcast, Real.rpow_natCast]
  simpa [w, hpow, Real.rpow_natCast] using hmean
