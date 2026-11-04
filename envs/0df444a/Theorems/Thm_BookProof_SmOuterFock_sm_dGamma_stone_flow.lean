-- Prove2me | Theorems.Thm_BookProof_SmOuterFock_sm_dGamma_stone_flow
-- name    : BookProof.SmOuterFock.sm_dGamma_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-03T22:37:59.344865+00:00
-- url     : https://prove2.me/theorems/1a4f1de3-a9d3-48a1-98f0-37bf677301d2
-- title:
--   `BookProof.SmOuterFock.sm_dGamma_stone_flow` (P : SmParams) : ∃ (T : UnboundedSelfAdjoint smFockSpace) (U : ℝ → (smFockSpace →L[ℂ] smFockSpace)), IsStoneFlow T U
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOuterFock`.
--
--   `BookProof.SmOuterFock.sm_dGamma_stone_flow` (P : SmParams) : ∃ (T : UnboundedSelfAdjoint smFockSpace) (U : ℝ → (smFockSpace →L[ℂ] smFockSpace)), IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.SmOuterFock.sm_dGamma_stone_flow`.

-- Generated from ChapterSmOuterFock.lean — theorem BookProof.SmOuterFock.sm_dGamma_stone_flow
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterSmOuterFock
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSmHamiltonian
open BookProof.HermiteProductCore
open BookProof.SmHamiltonian
open BookProof.StoneBridge
open BookProof.YangMillsFriedrichs



open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge
open BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.SmOuterFock.sm_dGamma_stone_flow (P : SmParams) :
    ∃ (T : UnboundedSelfAdjoint smFockSpace) (U : ℝ → (smFockSpace →L[ℂ] smFockSpace)),
      IsStoneFlow T U := by sorry
