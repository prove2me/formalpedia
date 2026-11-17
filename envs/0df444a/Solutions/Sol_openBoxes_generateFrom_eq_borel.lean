-- Prove2me | solution 1 for openBoxes_generateFrom_eq_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:23:05.113291+00:00
-- url     : https://prove2.me/submissions/eb344c89-cdd4-4447-a38f-c6f0da36275a

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Theorems.Thm_borelAlgebraReal_eq_borel
import Theorems.Thm_coordinateOpenBoxes_eq_openBoxes
import Theorems.Thm_realOpenIntervals_countablySpanning

-- import Mathlib.Data.Real.Pointwise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory MeasurableSpace

open scoped Pointwise


theorem solution (d : ℕ) :
    MeasurableSpace.generateFrom (openBoxes d) = borel (Fin d → ℝ) := by
  classical
  have hC : ∀ _ : Fin d, MeasurableSpace.generateFrom realOpenIntervals = borel ℝ := by
    intro _
    simpa [borelAlgebraReal] using borelAlgebraReal_eq_borel
  have hboxes :
      MeasurableSpace.generateFrom
          (Set.pi Set.univ '' Set.pi Set.univ (fun _ : Fin d => realOpenIntervals)) =
        MeasurableSpace.pi := by
    exact generateFrom_eq_pi
      (α := fun _ : Fin d => ℝ)
      (C := fun _ : Fin d => realOpenIntervals)
      hC
      (fun _ => realOpenIntervals_countablySpanning)
  rw [← coordinateOpenBoxes_eq_openBoxes d]
  exact hboxes.trans BorelSpace.measurable_eq