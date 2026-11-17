-- Prove2me | solution 1 for thm_2_7_borelAlgebraReal_le_generateFrom_strictClosed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:10:00.984609+00:00
-- url     : https://prove2.me/submissions/80ea498b-fd18-4eac-a1cd-bef1d785ea89

import Theorems.Thm_thm_2_7_openInterval_mem_generateFrom_strictClosed
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_7_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory

theorem solution :
    borelAlgebraReal ≤ MeasurableSpace.generateFrom realStrictClosedIntervals := by
  change MeasurableSpace.generateFrom realOpenIntervals ≤
    MeasurableSpace.generateFrom realStrictClosedIntervals
  refine MeasurableSpace.generateFrom_le ?_
  rintro S ⟨a, b, hab, rfl⟩
  exact thm_2_7_openInterval_mem_generateFrom_strictClosed hab
