-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_gint_gaussPolyDeriv_antisymm
-- name    : BookProof.QgHermiteCore.gint_gaussPolyDeriv_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:29:00.940611+00:00
-- url     : https://prove2.me/theorems/0534f8d7-bc2c-4db4-a366-dfbd8b5bb332
-- title:
--   (p q : Polynomial ℝ) : gint (gaussPolyDeriv p * q) = - gint (p * gaussPolyDeriv q)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.gint_gaussPolyDeriv_antisymm` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.gint_gaussPolyDeriv_antisymm
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.gint_gaussPolyDeriv_antisymm (p q : Polynomial ℝ) :
    gint (gaussPolyDeriv p * q) = - gint (p * gaussPolyDeriv q) := by sorry
