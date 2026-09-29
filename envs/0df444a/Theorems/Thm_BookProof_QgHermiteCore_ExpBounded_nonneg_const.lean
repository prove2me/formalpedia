-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_nonneg_const
-- name    : BookProof.QgHermiteCore.ExpBounded.nonneg_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:19:57.857092+00:00
-- url     : https://prove2.me/theorems/e4519172-80e3-4db3-98f8-56de3a6c5458
-- title:
--   {f : E → ℝ} {C c : ℝ} (h : ∀ x, |f x| ≤ C * Real.exp (c * ‖x‖)) : 0 ≤ C
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.ExpBounded.nonneg_const` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.ExpBounded.nonneg_const
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.ExpBounded.nonneg_const {f : E → ℝ} {C c : ℝ}
    (h : ∀ x, |f x| ≤ C * Real.exp (c * ‖x‖)) : 0 ≤ C := by sorry
