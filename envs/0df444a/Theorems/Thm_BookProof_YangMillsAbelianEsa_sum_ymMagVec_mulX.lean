-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianEsa_sum_ymMagVec_mulX
-- name    : BookProof.YangMillsAbelianEsa.sum_ymMagVec_mulX
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:41:46.729232+00:00
-- url     : https://prove2.me/theorems/5ef6185d-b603-43b0-8320-78effc6b1473
-- title:
--   `BookProof.YangMillsAbelianEsa.sum_ymMagVec_mulX` (m : Fin 24) : ∑ n : Fin 99, ((ymMagVec m n : ℝ) : ℂ) • mulXPoly (d := 99) n = mulOp (magPoly 0 (decodeSpace m) (decodeColor m))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianEsa`.
--
--   `BookProof.YangMillsAbelianEsa.sum_ymMagVec_mulX` (m : Fin 24) : ∑ n : Fin 99, ((ymMagVec m n : ℝ) : ℂ) • mulXPoly (d := 99) n = mulOp (magPoly 0 (decodeSpace m) (decodeColor m))
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianEsa.sum_ymMagVec_mulX`.

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.sum_ymMagVec_mulX
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
open BookProof.ChapterF7
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsHermite
open BookProof.YangMillsAbelianEsa



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

theorem BookProof.YangMillsAbelianEsa.sum_ymMagVec_mulX (m : Fin 24) :
    ∑ n : Fin 99, ((ymMagVec m n : ℝ) : ℂ) • mulXPoly (d := 99) n
      = mulOp (magPoly 0 (decodeSpace m) (decodeColor m)) := by sorry
