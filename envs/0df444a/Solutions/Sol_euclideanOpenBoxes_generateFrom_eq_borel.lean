-- Prove2me | solution 1 for euclideanOpenBoxes_generateFrom_eq_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:40:57.760993+00:00
-- url     : https://prove2.me/submissions/3c15557c-3cc9-4a0d-9c97-f8118f7f2109

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Theorems.Thm_openBoxes_generateFrom_eq_borel

-- import Mathlib.Data.Real.Pointwise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory MeasurableSpace

open scoped Pointwise


theorem solution (d : ℕ) :
    MeasurableSpace.generateFrom (euclideanOpenBoxes d) =
      borel (EuclideanSpace ℝ (Fin d)) := by
  let e : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ) := fun x i => x i
  have hcomap :
      MeasurableSpace.comap e (MeasurableSpace.generateFrom (openBoxes d)) =
        MeasurableSpace.generateFrom (euclideanOpenBoxes d) := by
    simpa [euclideanOpenBoxes, e] using
      (MeasurableSpace.comap_generateFrom (f := e) (s := openBoxes d))
  have hborel :
      borel (EuclideanSpace ℝ (Fin d)) =
        MeasurableSpace.comap e (borel (Fin d → ℝ)) := by
    simpa [e] using
      (borel_comap (α := EuclideanSpace ℝ (Fin d)) (β := Fin d → ℝ)
        (f := e) (t := inferInstance))
  calc
    MeasurableSpace.generateFrom (euclideanOpenBoxes d) =
        MeasurableSpace.comap e (MeasurableSpace.generateFrom (openBoxes d)) :=
      hcomap.symm
    _ = MeasurableSpace.comap e (borel (Fin d → ℝ)) := by
      rw [openBoxes_generateFrom_eq_borel d]
    _ = borel (EuclideanSpace ℝ (Fin d)) :=
      hborel.symm