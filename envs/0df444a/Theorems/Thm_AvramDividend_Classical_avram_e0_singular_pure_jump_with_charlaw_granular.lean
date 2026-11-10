-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_singular_pure_jump_with_charlaw_granular
-- name    : AvramDividend.Classical.avram_e0_singular_pure_jump_with_charlaw_granular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T19:02:21.090555+00:00
-- url     : https://prove2.me/theorems/e6f29abb-9d3a-4615-8608-630b034015e6
-- title:
--   Singular negative-jump Lévy process with its exact characteristic-function law
-- statement:
--   For the explicit negative-jump Levy density |z|^(-3/2) on (-1,0), construct the associated Levy measure and an actual probability-space pure-jump Levy process, retaining its exact Levy-Khintchine characteristic-function identity. The full Fourier law is needed for a subsequent original Avram-process construction; generic process existence alone discards it.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_ProbabilityTheory_exists_isLevyProcess_pureJump
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_singular_pure_jump_with_charlaw_granular :
    ∃ (ν : Measure ℝ) (hν : IsLevyMeasure ν),
      ν = volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0) ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧
        (∀ t, Measurable (X t)) ∧
        ∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (μ.map (X t)) ξ =
          Complex.exp (((t : ℝ) : ℂ) *
            (LevyKhintchineTriple.mk 0 0 ν hν).exponent ξ) := by sorry
