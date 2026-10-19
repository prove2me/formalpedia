-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_qgGradedFock_essentiallySelfAdjointOn
-- name    : BookProof.QuantumGravityFock.qgGradedFock_essentiallySelfAdjointOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:37:37.041954+00:00
-- url     : https://prove2.me/theorems/082fea70-05dd-43a0-b7f9-18c5ad35e22b
-- title:
--   `BookProof.QuantumGravityFock.qgGradedFock_essentiallySelfAdjointOn` (omega g : ℕ → ℝ) : EssentiallySelfAdjointOn (lpFiniteModes GradedIdx) ((lpFiniteModes GradedIdx).subtype.comp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.qgGradedFock_essentiallySelfAdjointOn` (omega g : ℕ → ℝ) : EssentiallySelfAdjointOn (lpFiniteModes GradedIdx) ((lpFiniteModes GradedIdx).subtype.comp (qgGradedHam omega g))
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.qgGradedFock_essentiallySelfAdjointOn`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGradedFock_essentiallySelfAdjointOn
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
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.QuantumGravityFock.qgGradedFock_essentiallySelfAdjointOn (omega g : ℕ → ℝ) :
    EssentiallySelfAdjointOn (lpFiniteModes GradedIdx)
      ((lpFiniteModes GradedIdx).subtype.comp (qgGradedHam omega g)) := by sorry
