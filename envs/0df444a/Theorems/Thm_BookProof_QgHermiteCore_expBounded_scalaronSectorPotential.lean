-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_expBounded_scalaronSectorPotential
-- name    : BookProof.QgHermiteCore.expBounded_scalaronSectorPotential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:07:21.703123+00:00
-- url     : https://prove2.me/theorems/55ba85da-a403-45bc-b5d5-b2e41a93db0f
-- title:
--   (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ) : ExpBounded (scalaronSectorPotential M alpha V3)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.expBounded_scalaronSectorPotential` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.expBounded_scalaronSectorPotential
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]





































open BookProof.HermiteProductCore

variable {d : ℕ}

theorem BookProof.QgHermiteCore.expBounded_scalaronSectorPotential (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ) :
    ExpBounded (scalaronSectorPotential M alpha V3) := by sorry
