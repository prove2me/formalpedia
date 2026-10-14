-- Prove2me | Theorems.Thm_BookProof_SmHamiltonian_realCoeff_smFormPoly
-- name    : BookProof.SmHamiltonian.realCoeff_smFormPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:58:19.232881+00:00
-- url     : https://prove2.me/theorems/e9284609-9558-478c-ae6e-0501c2c7d134
-- title:
--   `BookProof.SmHamiltonian.realCoeff_smFormPoly` (P : SmParams) (co : Fin 163 → Fin D) (r : SmForm) : RealCoeff (smFormPoly P co r)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHamiltonian`.
--
--   `BookProof.SmHamiltonian.realCoeff_smFormPoly` (P : SmParams) (co : Fin 163 → Fin D) (r : SmForm) : RealCoeff (smFormPoly P co r)
--
--   Formalization note: Lean 4 identifier `BookProof.SmHamiltonian.realCoeff_smFormPoly`.

-- Generated from ChapterSmHamiltonian.lean — theorem BookProof.SmHamiltonian.realCoeff_smFormPoly
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
open BookProof.SmHamiltonian



open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

variable {D : ℕ}

theorem BookProof.SmHamiltonian.realCoeff_smFormPoly (P : SmParams) (co : Fin 163 → Fin D) (r : SmForm) :
    RealCoeff (smFormPoly P co r) := by sorry
