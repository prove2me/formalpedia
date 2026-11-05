-- Prove2me | solution 1 for levy_foundations_bochnerIntegralIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:57:52.372658+00:00
-- url     : https://prove2.me/submissions/b1a36715-6d94-45fa-8aa3-0db0098c9c39

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Definitions.Def_levy_foundations_covarianceMatrix
import Definitions.Def_levy_foundations_isPositiveDefinite
import Theorems.Thm_levy_foundations_bochner

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Matrix Complex Filter
open scoped ComplexOrder

theorem solution
    (ψ : ℝ → ℂ) (hc : Continuous ψ)
    (hpd : LevyFoundations.isPositiveDefinite ψ) (h0 : ψ 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ t : ℝ, ψ t = ∫ x : ℝ,
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) ∂(μ : Measure ℝ) := by
  obtain ⟨μ, hμ⟩ := levy_foundations_bochner ψ hc hpd h0
  refine ⟨μ, ?_⟩
  intro t
  rw [← hμ t, MeasureTheory.charFun_apply_real]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  apply congrArg Complex.exp
  ring
