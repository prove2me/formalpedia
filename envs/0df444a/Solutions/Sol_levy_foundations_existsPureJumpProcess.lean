-- Prove2me | solution 1 for levy_foundations_existsPureJumpProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:16:45.181233+00:00
-- url     : https://prove2.me/submissions/05083bb8-d2ad-4959-9653-97f2a1c30497

import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_levy_foundations_sigmaFinite
import Theorems.Thm_ProbabilityTheory_exists_isPoissonPointFamily
import Theorems.Thm_ProbabilityTheory_isLevyProcess_levyJumpPath
import Theorems.Thm_ProbabilityTheory_measurable_levyJumpPath
import Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpPath

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- Transplant the source Poisson-path construction into the public Lévy definitions. -/
theorem solution (b : ℝ) {ν : Measure ℝ} (hν : LevyFoundations.isLevyMeasure ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (X : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure μ ∧ LevyFoundations.IsLevyProcess X μ ∧
      (∀ t, Measurable (X t)) ∧
      ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (μ.map (X t)) ξ =
          Complex.exp (((t : ℝ) : ℂ) *
            LevyFoundations.exponent
              (LevyFoundations.LevyKhintchineTriple.mk b 0 ν hν) ξ) := by
  have hν' : ProbabilityTheory.IsLevyMeasure ν := hν
  haveI : SigmaFinite ν := levy_foundations_sigmaFinite ν hν
  obtain ⟨Ω, mΩ, μ, K, P, hprob, hd⟩ :=
    ProbabilityTheory.exists_isPoissonPointFamily ((volume : Measure ℝ).prod ν)
  let Y := ProbabilityTheory.levyJumpPath hd hν' b
  have hsource : ProbabilityTheory.IsLevyProcess Y μ :=
    ProbabilityTheory.isLevyProcess_levyJumpPath hd hν' b
  have hpublic : LevyFoundations.IsLevyProcess Y μ := by
    refine ⟨hsource.start_zero, ?_, ?_, ?_⟩
    · exact hsource.indep_increments
    · exact hsource.stationary_increments
    · exact hsource.cadlag_ae
  refine ⟨Ω, mΩ, μ, Y, hprob, hpublic, ?_, ?_⟩
  · intro t
    exact ProbabilityTheory.measurable_levyJumpPath hd hν' b t
  · intro t ξ
    exact ProbabilityTheory.charFun_map_levyJumpPath hd hν' b t ξ
