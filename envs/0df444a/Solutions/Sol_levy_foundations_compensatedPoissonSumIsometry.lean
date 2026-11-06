-- Prove2me | solution 1 for levy_foundations_compensatedPoissonSumIsometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:16:53.776929+00:00
-- url     : https://prove2.me/submissions/64831983-2e3b-486a-ae80-f427255ee39a

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_compensatedPoissonSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E) (f : E → ℝ)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    ∫ ω, (LevyFoundations.compensatedPoissonSum m K X f ω) ^ 2 ∂μ =
      ∫ x, f x ^ 2 ∂m := by
  have hd' : ProbabilityTheory.IsPoissonPointFamily K X m μ :=
    ⟨hd.measurable_count, hd.measurable_point, hd.indep, hd.law_count, hd.law_point⟩
  exact ProbabilityTheory.integral_sq_compensatedPoissonSum hd' hf hf1 hf2
