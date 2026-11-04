-- Prove2me | Theorems.Thm_BookProof_SmOuterFock_smSector_friedrichs_extension
-- name    : BookProof.SmOuterFock.smSector_friedrichs_extension
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-03T22:36:54.780848+00:00
-- url     : https://prove2.me/theorems/ced3fbb9-ff21-4c10-b86d-01b8161d98a8
-- title:
--   `BookProof.SmOuterFock.smSector_friedrichs_extension` (P : SmParams) (n : ℕ) : ∃ (Dom : Submodule ℂ (L2d (n * 163))) (A : Dom →ₗ[ℂ] L2d (n * 163)), IsPositiveSelfAdjointExtension (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOuterFock`.
--
--   `BookProof.SmOuterFock.smSector_friedrichs_extension` (P : SmParams) (n : ℕ) : ∃ (Dom : Submodule ℂ (L2d (n * 163))) (A : Dom →ₗ[ℂ] L2d (n * 163)), IsPositiveSelfAdjointExtension (smSectorHam P n) A
--
--   Formalization note: Lean 4 identifier `BookProof.SmOuterFock.smSector_friedrichs_extension`.

-- Generated from ChapterSmOuterFock.lean — theorem BookProof.SmOuterFock.smSector_friedrichs_extension
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterSmOuterFock
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSmHamiltonian
open BookProof.HermiteProductCore
open BookProof.SmHamiltonian
open BookProof.YangMillsFriedrichs



open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge
open BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.SmOuterFock.smSector_friedrichs_extension (P : SmParams) (n : ℕ) :
    ∃ (Dom : Submodule ℂ (L2d (n * 163))) (A : Dom →ₗ[ℂ] L2d (n * 163)),
      IsPositiveSelfAdjointExtension (smSectorHam P n) A := by sorry
