-- Prove2me | Theorems.Thm_BookProof_SmHamiltonian_smPi_symmetricOn
-- name    : BookProof.SmHamiltonian.smPi_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:01:33.860991+00:00
-- url     : https://prove2.me/theorems/d95788fe-c135-4fe2-a21d-2470f19c06a1
-- title:
--   `BookProof.SmHamiltonian.smPi_symmetricOn` (m : Fin 40) : SymmetricOn (polyGaussCore (d := 163)) ((polyGaussCore (d := 163)).subtype.comp (smPi m))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHamiltonian`.
--
--   `BookProof.SmHamiltonian.smPi_symmetricOn` (m : Fin 40) : SymmetricOn (polyGaussCore (d := 163)) ((polyGaussCore (d := 163)).subtype.comp (smPi m))
--
--   Formalization note: Lean 4 identifier `BookProof.SmHamiltonian.smPi_symmetricOn`.

-- Generated from ChapterSmHamiltonian.lean — theorem BookProof.SmHamiltonian.smPi_symmetricOn
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsHermite
open BookProof.SmHamiltonian



open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

variable {D : ℕ}

theorem BookProof.SmHamiltonian.smPi_symmetricOn (m : Fin 40) :
    SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp (smPi m)) := by sorry
