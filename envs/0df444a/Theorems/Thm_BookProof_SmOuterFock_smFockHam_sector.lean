-- Prove2me | Theorems.Thm_BookProof_SmOuterFock_smFockHam_sector
-- name    : BookProof.SmOuterFock.smFockHam_sector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:38:11.780068+00:00
-- url     : https://prove2.me/theorems/4aa0065c-a3ed-4086-9ebf-7f56d3a172a2
-- title:
--   `BookProof.SmOuterFock.smFockHam_sector` (P : SmParams) (x : smFockCore) (n : ℕ) : ((smFockHam P x : smFockSpace) : ∀ n : ℕ, L2d (n * 163)) n = smSectorHam P n ⟨((x : smFockSpace)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOuterFock`.
--
--   `BookProof.SmOuterFock.smFockHam_sector` (P : SmParams) (x : smFockCore) (n : ℕ) : ((smFockHam P x : smFockSpace) : ∀ n : ℕ, L2d (n * 163)) n = smSectorHam P n ⟨((x : smFockSpace) : ∀ n : ℕ, L2d (n * 163)) n, x.2.2 n⟩
--
--   Formalization note: Lean 4 identifier `BookProof.SmOuterFock.smFockHam_sector`.

-- Generated from ChapterSmOuterFock.lean — theorem BookProof.SmOuterFock.smFockHam_sector
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

theorem BookProof.SmOuterFock.smFockHam_sector (P : SmParams) (x : smFockCore) (n : ℕ) :
    ((smFockHam P x : smFockSpace) : ∀ n : ℕ, L2d (n * 163)) n
      = smSectorHam P n ⟨((x : smFockSpace) : ∀ n : ℕ, L2d (n * 163)) n, x.2.2 n⟩ := by sorry
