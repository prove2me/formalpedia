-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_qgGradedFock_esa
-- name    : BookProof.QuantumGravityFock.qgGradedFock_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:37:56.650714+00:00
-- url     : https://prove2.me/theorems/8fb87127-22fc-4c0f-bf82-591de8718907
-- title:
--   `BookProof.QuantumGravityFock.qgGradedFock_esa` (omega g : ℕ → ℝ) : HasZeroDeficiencyOn (lpFiniteModes GradedIdx) (qgGradedHam omega g)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.qgGradedFock_esa` (omega g : ℕ → ℝ) : HasZeroDeficiencyOn (lpFiniteModes GradedIdx) (qgGradedHam omega g)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.qgGradedFock_esa`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGradedFock_esa
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
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section

theorem BookProof.QuantumGravityFock.qgGradedFock_esa (omega g : ℕ → ℝ) :
    HasZeroDeficiencyOn (lpFiniteModes GradedIdx) (qgGradedHam omega g) := by sorry
