-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_harmCore_symmetricOn
-- name    : BookProof.SqSumFarisLavine.harmCore_symmetricOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T09:13:09.124691+00:00
-- url     : https://prove2.me/theorems/c58c2bc2-d435-4efc-b83c-ee1e1990f057
-- title:
--   The Lean 4 theorem `harmCore_symmetricOn` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmCore_symmetricOn` in the `ChapterSqSumFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.harmCore_symmetricOn
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteQuadraticEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.SqSumFarisLavine

variable {D : ℕ} {R : Type*} [Fintype R]



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.HermiteQuadraticEsa
open BookProof.QgOuterFock
open BookProof.GaussCoreQuadBounds

noncomputable section

theorem BookProof.SqSumFarisLavine.harmCore_symmetricOn : SymmetricOn (polyGaussCore (d := D)) (harmCore (d := D)) := by sorry
