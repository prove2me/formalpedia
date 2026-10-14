-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianEsa_ymAbelianPoly_apply
-- name    : BookProof.YangMillsAbelianEsa.ymAbelianPoly_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:41:31.268075+00:00
-- url     : https://prove2.me/theorems/5bb3a441-1171-4704-97d6-53e7b56d45bf
-- title:
--   `BookProof.YangMillsAbelianEsa.ymAbelianPoly_apply` (p : MvPolynomial (Fin 99) ℂ) : ymAbelianPoly p = ((1 / 2 : ℝ) : ℂ) • ((∑ m : Fin 24, YangMillsHermite.momOp (ymMomIdx m) (YangM
-- statement:
--   Prove the following Lean 4 theorem from `ChapterYangMillsAbelianEsa`.
--
--   `BookProof.YangMillsAbelianEsa.ymAbelianPoly_apply` (p : MvPolynomial (Fin 99) ℂ) : ymAbelianPoly p = ((1 / 2 : ℝ) : ℂ) • ((∑ m : Fin 24, YangMillsHermite.momOp (ymMomIdx m) (YangMillsHermite.momOp (ymMomIdx m) p)) + ∑ m : Fin 24, mulOp (magPoly 0 (decodeSpace m) (decodeColor m)) (mulOp (magPoly 0 (decodeSpace m) (decodeColor m)) p))
--
--   Formalization note: Lean 4 identifier `BookProof.YangMillsAbelianEsa.ymAbelianPoly_apply`.

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.ymAbelianPoly_apply
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

theorem BookProof.YangMillsAbelianEsa.ymAbelianPoly_apply (p : MvPolynomial (Fin 99) ℂ) :
    ymAbelianPoly p
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ m : Fin 24,
              YangMillsHermite.momOp (ymMomIdx m) (YangMillsHermite.momOp (ymMomIdx m) p))
            + ∑ m : Fin 24, mulOp (magPoly 0 (decodeSpace m) (decodeColor m))
                (mulOp (magPoly 0 (decodeSpace m) (decodeColor m)) p)) := by sorry
