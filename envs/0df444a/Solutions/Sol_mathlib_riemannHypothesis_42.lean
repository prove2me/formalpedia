-- Prove2me | solution 42 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:57.961333+00:00
-- url     : https://prove2.me/submissions/f2abc805-5655-476e-8921-152606baf890
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MasulloRH_realTraceIntegrand_integrable
import Theorems.Thm_MasulloRH_primePowerTraceTerm_finite_support
import Theorems.Thm_MasulloRH_spectral_trace_hasSum
import Mathlib.Tactic.Abel
import Theorems.Thm_MasulloRH_trace_formula_rational_iff_RH

-- Step 1: `MasulloRH.spectral_trace_hasSum` implies `MasulloRH.trace_formula_rational` (accepted reduction of `MasulloRH.trace_formula_rational`).
section

open MasulloRH MeasureTheory Set

theorem MasulloRH.trace_formula_rational (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  have h := spectral_trace_hasSum α hα φ hφ
  refine ⟨realTraceIntegrand_integrable φ hφ,
    summable_of_hasFiniteSupport (primePowerTraceTerm_finite_support φ hφ), h.summable, ?_⟩
  rw [h.tsum_eq]
  abel

end

-- Step 2: `MasulloRH.trace_formula_rational` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  MasulloRH.trace_formula_rational_iff_RH.mp
    (fun α hα φ hφ => MasulloRH.trace_formula_rational α hα φ hφ)

end
