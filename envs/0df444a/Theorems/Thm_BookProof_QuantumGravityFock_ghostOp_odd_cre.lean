-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_ghostOp_odd_cre
-- name    : BookProof.QuantumGravityFock.ghostOp_odd_cre
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:36:51.854001+00:00
-- url     : https://prove2.me/theorems/dcc4906d-4bd7-4d90-83c0-09b9a1b6c7ca
-- title:
--   `BookProof.QuantumGravityFock.ghostOp_odd_cre` (j : ℕ) (z : QGGraded) : qgGrade (ghostOp (fermCre j) z) = - ghostOp (fermCre j) (qgGrade z)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.ghostOp_odd_cre` (j : ℕ) (z : QGGraded) : qgGrade (ghostOp (fermCre j) z) = - ghostOp (fermCre j) (qgGrade z)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.ghostOp_odd_cre`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.ghostOp_odd_cre
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterQuantumGravityFock
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section

theorem BookProof.QuantumGravityFock.ghostOp_odd_cre (j : ℕ) (z : QGGraded) :
    qgGrade (ghostOp (fermCre j) z) = - ghostOp (fermCre j) (qgGrade z) := by sorry
