-- Prove2me | Theorems.Thm_BookProof_SmHamiltonian_smField_symmetricOn
-- name    : BookProof.SmHamiltonian.smField_symmetricOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T14:13:19.70299+00:00
-- url     : https://prove2.me/theorems/b724e1b5-dbd9-4965-9377-2d9fb282927e
-- title:
--   `BookProof.SmHamiltonian.smField_symmetricOn` (P : SmParams) (r : Fin 49) : SymmetricOn (polyGaussCore (d := 163)) ((polyGaussCore (d := 163)).subtype.comp (smField P r))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHamiltonian`.
--
--   `BookProof.SmHamiltonian.smField_symmetricOn` (P : SmParams) (r : Fin 49) : SymmetricOn (polyGaussCore (d := 163)) ((polyGaussCore (d := 163)).subtype.comp (smField P r))
--
--   Formalization note: Lean 4 identifier `BookProof.SmHamiltonian.smField_symmetricOn`.

-- Generated from ChapterSmHamiltonian.lean — theorem BookProof.SmHamiltonian.smField_symmetricOn
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.ChapterF7
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite
open BookProof.SmHamiltonian



open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

variable {D : ℕ}

theorem BookProof.SmHamiltonian.smField_symmetricOn (P : SmParams) (r : Fin 49) :
    SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp (smField P r)) := by sorry
