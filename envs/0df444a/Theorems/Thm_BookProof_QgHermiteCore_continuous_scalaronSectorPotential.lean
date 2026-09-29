-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_continuous_scalaronSectorPotential
-- name    : BookProof.QgHermiteCore.continuous_scalaronSectorPotential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:44:46.692023+00:00
-- url     : https://prove2.me/theorems/bc21b245-c7ff-4df1-bd45-0341c151b23a
-- title:
--   (M alpha : ℝ) (V3 : Polynomial ℝ) : Continuous (scalaronSectorPotential M alpha V3)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.continuous_scalaronSectorPotential` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.continuous_scalaronSectorPotential
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]





































open BookProof.HermiteProductCore

variable {d : ℕ}

theorem BookProof.QgHermiteCore.continuous_scalaronSectorPotential (M alpha : ℝ) (V3 : Polynomial ℝ) :
    Continuous (scalaronSectorPotential M alpha V3) := by sorry
