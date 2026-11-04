-- Prove2me | Theorems.Thm_BookProof_SmOuterFock_smSectorHam_symmetricOn
-- name    : BookProof.SmOuterFock.smSectorHam_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:36:52.6022+00:00
-- url     : https://prove2.me/theorems/6879aace-a141-48e8-b183-d5078d1a9eea
-- title:
--   `BookProof.SmOuterFock.smSectorHam_symmetricOn` (P : SmParams) (n : ℕ) : SymmetricOn (polyGaussCore (d := n * 163)) (smSectorHam P n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOuterFock`.
--
--   `BookProof.SmOuterFock.smSectorHam_symmetricOn` (P : SmParams) (n : ℕ) : SymmetricOn (polyGaussCore (d := n * 163)) (smSectorHam P n)
--
--   Formalization note: Lean 4 identifier `BookProof.SmOuterFock.smSectorHam_symmetricOn`.

-- Generated from ChapterSmOuterFock.lean — theorem BookProof.SmOuterFock.smSectorHam_symmetricOn
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
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.SmOuterFock.smSectorHam_symmetricOn (P : SmParams) (n : ℕ) :
    SymmetricOn (polyGaussCore (d := n * 163)) (smSectorHam P n) := by sorry
