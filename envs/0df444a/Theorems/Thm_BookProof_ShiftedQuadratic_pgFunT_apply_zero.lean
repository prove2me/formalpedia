-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_pgFunT_apply_zero
-- name    : BookProof.ShiftedQuadratic.pgFunT_apply_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:44:15.523992+00:00
-- url     : https://prove2.me/theorems/230e99ff-77fc-4047-8e38-9517f7f393ec
-- title:
--   `BookProof.ShiftedQuadratic.pgFunT_apply_zero` (a k : Vd d) (x : Vd d) : pgFunT a k 0 x = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.pgFunT_apply_zero` (a k : Vd d) (x : Vd d) : pgFunT a k 0 x = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.pgFunT_apply_zero`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.pgFunT_apply_zero
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
open BookProof.MixedLinearEsa
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadratic.pgFunT_apply_zero (a k : Vd d) (x : Vd d) : pgFunT a k 0 x = 0 := by sorry
