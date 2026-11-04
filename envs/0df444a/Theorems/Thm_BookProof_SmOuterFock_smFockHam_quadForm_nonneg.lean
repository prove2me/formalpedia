-- Prove2me | Theorems.Thm_BookProof_SmOuterFock_smFockHam_quadForm_nonneg
-- name    : BookProof.SmOuterFock.smFockHam_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:36:59.191223+00:00
-- url     : https://prove2.me/theorems/dbcb0d9d-eb2f-4c41-bcba-19ca086dd764
-- title:
--   `BookProof.SmOuterFock.smFockHam_quadForm_nonneg` (P : SmParams) (x : smFockCore) : 0 ≤ quadForm (smFockHam P) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOuterFock`.
--
--   `BookProof.SmOuterFock.smFockHam_quadForm_nonneg` (P : SmParams) (x : smFockCore) : 0 ≤ quadForm (smFockHam P) x
--
--   Formalization note: Lean 4 identifier `BookProof.SmOuterFock.smFockHam_quadForm_nonneg`.

-- Generated from ChapterSmOuterFock.lean — theorem BookProof.SmOuterFock.smFockHam_quadForm_nonneg
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterSmOuterFock
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSmHamiltonian
open BookProof.HermiteProductCore
open BookProof.SmHamiltonian



open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge
open BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.SmOuterFock.smFockHam_quadForm_nonneg (P : SmParams) (x : smFockCore) :
    0 ≤ quadForm (smFockHam P) x := by sorry
