-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_qgGhostCar_of_ne
-- name    : BookProof.QuantumGravityFock.qgGhostCar_of_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:35:57.609994+00:00
-- url     : https://prove2.me/theorems/a0bb24c4-c0d0-4632-8479-861c6a3e826f
-- title:
--   `BookProof.QuantumGravityFock.qgGhostCar_of_ne` {j k : ℕ} (h : j ≠ k) (z : QGGraded) : ghostOp (fermAnn j) (ghostOp (fermCre k) z) + ghostOp (fermCre k) (ghostOp (fermAnn j) z) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.qgGhostCar_of_ne` {j k : ℕ} (h : j ≠ k) (z : QGGraded) : ghostOp (fermAnn j) (ghostOp (fermCre k) z) + ghostOp (fermCre k) (ghostOp (fermAnn j) z) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.qgGhostCar_of_ne`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGhostCar_of_ne
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

theorem BookProof.QuantumGravityFock.qgGhostCar_of_ne {j k : ℕ} (h : j ≠ k) (z : QGGraded) :
    ghostOp (fermAnn j) (ghostOp (fermCre k) z) + ghostOp (fermCre k) (ghostOp (fermAnn j) z)
      = 0 := by sorry
