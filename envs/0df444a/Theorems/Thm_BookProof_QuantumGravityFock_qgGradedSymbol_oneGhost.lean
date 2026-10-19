-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_qgGradedSymbol_oneGhost
-- name    : BookProof.QuantumGravityFock.qgGradedSymbol_oneGhost
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:37:07.458907+00:00
-- url     : https://prove2.me/theorems/b376a031-ed64-47f7-adde-9379cfe8bfab
-- title:
--   `BookProof.QuantumGravityFock.qgGradedSymbol_oneGhost` (omega g : ℕ → ℝ) (a : ℕ) : qgGradedSymbol omega g (0, ({a} : FermConf)) = g a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.qgGradedSymbol_oneGhost` (omega g : ℕ → ℝ) (a : ℕ) : qgGradedSymbol omega g (0, ({a} : FermConf)) = g a
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.qgGradedSymbol_oneGhost`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGradedSymbol_oneGhost
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
import Definitions.Def_ChapterFockSecondQuantization
import Mathlib
import Definitions.Def_ChapterQuantumGravityFock
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterYangMillsGhostSector
open BookProof.FockOneParticleGap
open BookProof.YangMillsGhost
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section

theorem BookProof.QuantumGravityFock.qgGradedSymbol_oneGhost (omega g : ℕ → ℝ) (a : ℕ) :
    qgGradedSymbol omega g (0, ({a} : FermConf)) = g a := by sorry
