-- Prove2me | Theorems.Thm_BookProof_SmHamiltonian_smHamiltonian_symmetricOn
-- name    : BookProof.SmHamiltonian.smHamiltonian_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:15:47.578153+00:00
-- url     : https://prove2.me/theorems/09efdc79-fb80-44b7-af82-fa85bd12f61e
-- title:
--   `BookProof.SmHamiltonian.smHamiltonian_symmetricOn` (P : SmParams) : SymmetricOn (polyGaussCore (d := 163)) (smHamiltonian P)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHamiltonian`.
--
--   `BookProof.SmHamiltonian.smHamiltonian_symmetricOn` (P : SmParams) : SymmetricOn (polyGaussCore (d := 163)) (smHamiltonian P)
--
--   Formalization note: Lean 4 identifier `BookProof.SmHamiltonian.smHamiltonian_symmetricOn`.

-- Generated from ChapterSmHamiltonian.lean — theorem BookProof.SmHamiltonian.smHamiltonian_symmetricOn
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs
open BookProof.SmHamiltonian



open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

variable {D : ℕ}

theorem BookProof.SmHamiltonian.smHamiltonian_symmetricOn (P : SmParams) :
    SymmetricOn (polyGaussCore (d := 163)) (smHamiltonian P) := by sorry
