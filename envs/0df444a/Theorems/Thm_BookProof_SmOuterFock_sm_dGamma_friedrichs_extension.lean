-- Prove2me | Theorems.Thm_BookProof_SmOuterFock_sm_dGamma_friedrichs_extension
-- name    : BookProof.SmOuterFock.sm_dGamma_friedrichs_extension
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-03T22:51:35.861251+00:00
-- url     : https://prove2.me/theorems/af263f8d-6f19-4365-a922-9a88d29ce4cf
-- title:
--   `BookProof.SmOuterFock.sm_dGamma_friedrichs_extension` (P : SmParams) : ∃ (Dom : Submodule ℂ smFockSpace) (A : Dom →ₗ[ℂ] smFockSpace), IsPositiveSelfAdjointExtension (smFockHam P)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOuterFock`.
--
--   `BookProof.SmOuterFock.sm_dGamma_friedrichs_extension` (P : SmParams) : ∃ (Dom : Submodule ℂ smFockSpace) (A : Dom →ₗ[ℂ] smFockSpace), IsPositiveSelfAdjointExtension (smFockHam P) A
--
--   Formalization note: Lean 4 identifier `BookProof.SmOuterFock.sm_dGamma_friedrichs_extension`.

-- Generated from ChapterSmOuterFock.lean — theorem BookProof.SmOuterFock.sm_dGamma_friedrichs_extension
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

theorem BookProof.SmOuterFock.sm_dGamma_friedrichs_extension (P : SmParams) :
    ∃ (Dom : Submodule ℂ smFockSpace) (A : Dom →ₗ[ℂ] smFockSpace),
      IsPositiveSelfAdjointExtension (smFockHam P) A := by sorry
