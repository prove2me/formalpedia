-- Prove2me | solution 1 for thm_6_6_complex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:17:17.904271+00:00
-- url     : https://prove2.me/submissions/51aeaa03-7ed1-4c16-95d4-2f2fea4b15c0

import Theorems.Thm_Thm66Support_complexTextbookIntegrable_iff_complexAbsIntegral_lt_top
import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_6_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
namespace Thm66Support
open Def66RealSupport
end Thm66Support

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ)
    (hZm : Measurable Z) :
    ((∫⁻ ω, ENNReal.ofReal |(Z ω).re| ∂μ) < ⊤ ∧
        (∫⁻ ω, ENNReal.ofReal |(Z ω).im| ∂μ) < ⊤) ↔
      (∫⁻ ω, ENNReal.ofReal ‖Z ω‖ ∂μ) < ⊤ := by
  simpa [Thm66Support.complexTextbookIntegrable, Thm66Support.complexAbsIntegral,
    Thm66Support.realPartAbsIntegral, Thm66Support.imagPartAbsIntegral]
    using Thm66Support.complexTextbookIntegrable_iff_complexAbsIntegral_lt_top μ Z hZm
