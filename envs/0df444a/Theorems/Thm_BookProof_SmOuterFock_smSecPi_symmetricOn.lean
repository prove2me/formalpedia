-- Prove2me | Theorems.Thm_BookProof_SmOuterFock_smSecPi_symmetricOn
-- name    : BookProof.SmOuterFock.smSecPi_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:37:29.698501+00:00
-- url     : https://prove2.me/theorems/d2b47ad9-f317-4f62-b10d-128ca37730f8
-- title:
--   `BookProof.SmOuterFock.smSecPi_symmetricOn` (n : ℕ) (m : Fin (n * 40)) : SymmetricOn (polyGaussCore (d := n * 163)) ((polyGaussCore (d := n * 163)).subtype.comp (smSecPi n m))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmOuterFock`.
--
--   `BookProof.SmOuterFock.smSecPi_symmetricOn` (n : ℕ) (m : Fin (n * 40)) : SymmetricOn (polyGaussCore (d := n * 163)) ((polyGaussCore (d := n * 163)).subtype.comp (smSecPi n m))
--
--   Formalization note: Lean 4 identifier `BookProof.SmOuterFock.smSecPi_symmetricOn`.

-- Generated from ChapterSmOuterFock.lean — theorem BookProof.SmOuterFock.smSecPi_symmetricOn
import Definitions.Def_ChapterSmOneParticle
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
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSmHamiltonian
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.SmHamiltonian
open BookProof.YangMillsHermite



open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge
open BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.SmOuterFock.smSecPi_symmetricOn (n : ℕ) (m : Fin (n * 40)) :
    SymmetricOn (polyGaussCore (d := n * 163))
      ((polyGaussCore (d := n * 163)).subtype.comp (smSecPi n m)) := by sorry
