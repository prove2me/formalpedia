-- Prove2me | Theorems.Thm_BookProof_SmOuterFock_smFockHam_number_conserving
-- name    : BookProof.SmOuterFock.smFockHam_number_conserving
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-03T22:37:02.501144+00:00
-- url     : https://prove2.me/theorems/1d50fff7-5ed6-44bf-baf6-16e2e487a7b2
-- title:
--   `BookProof.SmOuterFock.smFockHam_number_conserving` (P : SmParams) (x : smFockCore) {n : ℕ} (hx : ∀ m, m ≠ n → ((x : smFockSpace) : ∀ m : ℕ, L2d (m * 163)) m = 0) (m : ℕ) (hm : m ≠
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOuterFock`.
--
--   `BookProof.SmOuterFock.smFockHam_number_conserving` (P : SmParams) (x : smFockCore) {n : ℕ} (hx : ∀ m, m ≠ n → ((x : smFockSpace) : ∀ m : ℕ, L2d (m * 163)) m = 0) (m : ℕ) (hm : m ≠ n) : ((smFockHam P x : smFockSpace) : ∀ m : ℕ, L2d (m * 163)) m = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmOuterFock.smFockHam_number_conserving`.

-- Generated from ChapterSmOuterFock.lean — theorem BookProof.SmOuterFock.smFockHam_number_conserving
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

theorem BookProof.SmOuterFock.smFockHam_number_conserving (P : SmParams) (x : smFockCore)
    {n : ℕ} (hx : ∀ m, m ≠ n → ((x : smFockSpace) : ∀ m : ℕ, L2d (m * 163)) m = 0) (m : ℕ)
    (hm : m ≠ n) : ((smFockHam P x : smFockSpace) : ∀ m : ℕ, L2d (m * 163)) m = 0 := by sorry
