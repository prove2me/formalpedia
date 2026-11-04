-- Prove2me | Theorems.Thm_BookProof_SmOuterFock_smFockCore_dense
-- name    : BookProof.SmOuterFock.smFockCore_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:36:57.691521+00:00
-- url     : https://prove2.me/theorems/17b48090-7d2e-4b20-9c71-4365595f04ad
-- title:
--   `BookProof.SmOuterFock.smFockCore_dense` : Dense ((smFockCore : Submodule ℂ smFockSpace) : Set smFockSpace)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOuterFock`.
--
--   `BookProof.SmOuterFock.smFockCore_dense` : Dense ((smFockCore : Submodule ℂ smFockSpace) : Set smFockSpace)
--
--   Formalization note: Lean 4 identifier `BookProof.SmOuterFock.smFockCore_dense`.

-- Generated from ChapterSmOuterFock.lean — theorem BookProof.SmOuterFock.smFockCore_dense
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterSmHamiltonian
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
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSmHamiltonian
open BookProof.HermiteProductCore



open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge
open BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.SmOuterFock.smFockCore_dense :
    Dense ((smFockCore : Submodule ℂ smFockSpace) : Set smFockSpace) := by sorry
