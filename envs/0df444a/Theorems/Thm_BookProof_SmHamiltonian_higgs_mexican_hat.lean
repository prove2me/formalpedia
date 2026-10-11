-- Prove2me | Theorems.Thm_BookProof_SmHamiltonian_higgs_mexican_hat
-- name    : BookProof.SmHamiltonian.higgs_mexican_hat
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:13:42.934284+00:00
-- url     : https://prove2.me/theorems/d5ddc219-4bb9-4ab0-be68-2a6cc8ab3c4f
-- title:
--   `BookProof.SmHamiltonian.higgs_mexican_hat` (lam mu q : ℝ) (hlam : 0 < lam) : lam / 4 * (q - mu ^ 2 / lam) ^ 2 = -(mu ^ 2 / 2) * q + lam / 4 * q ^ 2 + mu ^ 4 / (4 * lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHamiltonian`.
--
--   `BookProof.SmHamiltonian.higgs_mexican_hat` (lam mu q : ℝ) (hlam : 0 < lam) : lam / 4 * (q - mu ^ 2 / lam) ^ 2 = -(mu ^ 2 / 2) * q + lam / 4 * q ^ 2 + mu ^ 4 / (4 * lam)
--
--   Formalization note: Lean 4 identifier `BookProof.SmHamiltonian.higgs_mexican_hat`.

-- Generated from ChapterSmHamiltonian.lean — theorem BookProof.SmHamiltonian.higgs_mexican_hat
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
open BookProof.SmHamiltonian



open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

variable {D : ℕ}

theorem BookProof.SmHamiltonian.higgs_mexican_hat (lam mu q : ℝ) (hlam : 0 < lam) :
    lam / 4 * (q - mu ^ 2 / lam) ^ 2
      = -(mu ^ 2 / 2) * q + lam / 4 * q ^ 2 + mu ^ 4 / (4 * lam) := by sorry
