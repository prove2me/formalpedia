-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_gint_gaussPolyDeriv_two_symm
-- name    : BookProof.QgHermiteCore.gint_gaussPolyDeriv_two_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:46:46.020617+00:00
-- url     : https://prove2.me/theorems/d2b25ebb-97ce-4ccb-b850-c2268dda091b
-- title:
--   (p q : Polynomial ℝ) : gint (gaussPolyDeriv (gaussPolyDeriv p) * q) = gint (p * gaussPolyDeriv (gaussPolyDeriv q))
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.gint_gaussPolyDeriv_two_symm` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.gint_gaussPolyDeriv_two_symm
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.gint_gaussPolyDeriv_two_symm (p q : Polynomial ℝ) :
    gint (gaussPolyDeriv (gaussPolyDeriv p) * q)
      = gint (p * gaussPolyDeriv (gaussPolyDeriv q)) := by sorry
