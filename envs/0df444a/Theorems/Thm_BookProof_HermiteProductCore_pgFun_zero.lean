-- Prove2me | Theorems.Thm_BookProof_HermiteProductCore_pgFun_zero
-- name    : BookProof.HermiteProductCore.pgFun_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:48:26.38934+00:00
-- url     : https://prove2.me/theorems/842ae438-b499-4885-be9c-3df8c70530f6
-- title:
--   The Lean 4 theorem `pgFun_zero` in the `ChapterHermiteProductCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgFun_zero` in the `ChapterHermiteProductCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductCore.lean

-- Generated from ChapterHermiteProductCore.lean — theorem BookProof.HermiteProductCore.pgFun_zero
import Mathlib
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore







open MeasureTheory Complex MvPolynomial BookProof.HermiteCore
open scoped FourierTransform
open SchwartzMap

noncomputable section



variable {d : ℕ}

theorem BookProof.HermiteProductCore.pgFun_zero : pgFun (0 : MvPolynomial (Fin d) ℂ) = 0 := by sorry
