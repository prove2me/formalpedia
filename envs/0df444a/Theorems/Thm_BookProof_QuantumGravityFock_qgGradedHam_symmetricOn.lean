-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_qgGradedHam_symmetricOn
-- name    : BookProof.QuantumGravityFock.qgGradedHam_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:38:00.652915+00:00
-- url     : https://prove2.me/theorems/579a0f9d-ac1f-4c71-b7c0-eea47235ad89
-- title:
--   `BookProof.QuantumGravityFock.qgGradedHam_symmetricOn` (omega g : ℕ → ℝ) : SymmetricOn (lpFiniteModes GradedIdx) ((lpFiniteModes GradedIdx).subtype.comp (qgGradedHam omega g))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.qgGradedHam_symmetricOn` (omega g : ℕ → ℝ) : SymmetricOn (lpFiniteModes GradedIdx) ((lpFiniteModes GradedIdx).subtype.comp (qgGradedHam omega g))
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.qgGradedHam_symmetricOn`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGradedHam_symmetricOn
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
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section

theorem BookProof.QuantumGravityFock.qgGradedHam_symmetricOn (omega g : ℕ → ℝ) :
    SymmetricOn (lpFiniteModes GradedIdx)
      ((lpFiniteModes GradedIdx).subtype.comp (qgGradedHam omega g)) := by sorry
