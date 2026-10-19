-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_qgGhostCar_book
-- name    : BookProof.QuantumGravityFock.qgGhostCar_book
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:36:34.61264+00:00
-- url     : https://prove2.me/theorems/2eabf178-93ce-44ee-b041-97ccf7e1c15b
-- title:
--   `BookProof.QuantumGravityFock.qgGhostCar_book` (a b : Fin qgGhostModes) (z : QGGraded) : ghostOp (fermAnn a.val) (ghostOp (fermCre b.val) z) + ghostOp (fermCre b.val) (ghostOp (fer
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.qgGhostCar_book` (a b : Fin qgGhostModes) (z : QGGraded) : ghostOp (fermAnn a.val) (ghostOp (fermCre b.val) z) + ghostOp (fermCre b.val) (ghostOp (fermAnn a.val) z) = if a = b then z else 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.qgGhostCar_book`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGhostCar_book
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

theorem BookProof.QuantumGravityFock.qgGhostCar_book (a b : Fin qgGhostModes) (z : QGGraded) :
    ghostOp (fermAnn a.val) (ghostOp (fermCre b.val) z)
        + ghostOp (fermCre b.val) (ghostOp (fermAnn a.val) z)
      = if a = b then z else 0 := by sorry
