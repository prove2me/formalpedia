-- Prove2me | Theorems.Thm_BookProof_QuantumGravityFock_qgGradedHam_isSymmetricDom
-- name    : BookProof.QuantumGravityFock.qgGradedHam_isSymmetricDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:37:57.703463+00:00
-- url     : https://prove2.me/theorems/99ca2124-e87c-493d-a81a-6eb0e7698bfe
-- title:
--   `BookProof.QuantumGravityFock.qgGradedHam_isSymmetricDom` (omega g : ℕ → ℝ) : IsSymmetricDom (qgGradedHam omega g)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityFock`.
--
--   `BookProof.QuantumGravityFock.qgGradedHam_isSymmetricDom` (omega g : ℕ → ℝ) : IsSymmetricDom (qgGradedHam omega g)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityFock.qgGradedHam_isSymmetricDom`.

-- Generated from ChapterQuantumGravityFock.lean — theorem BookProof.QuantumGravityFock.qgGradedHam_isSymmetricDom
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesFockSpace
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
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.QuantumGravityFock



open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.FockOfFock BookProof.NavierStokesFlow.FullEsa
open BookProof.FarisLavine BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization

noncomputable section

theorem BookProof.QuantumGravityFock.qgGradedHam_isSymmetricDom (omega g : ℕ → ℝ) :
    IsSymmetricDom (qgGradedHam omega g) := by sorry
