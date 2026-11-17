-- Prove2me | solution 1 for thm_6_6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:39:05.537746+00:00
-- url     : https://prove2.me/submissions/9602afe2-94d6-4a21-b724-741a634ef377

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

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal)
    (_hXm : Measurable X) :
    ((∫⁻ ω, (X ω).toENNReal ∂μ) < ⊤ ∧
        (∫⁻ ω, (-X ω).toENNReal ∂μ) < ⊤) ↔
      (∫⁻ ω, (X ω).toENNReal ∂μ) + (∫⁻ ω, (-X ω).toENNReal ∂μ) < ⊤ := by
  simp only [ENNReal.add_lt_top]
