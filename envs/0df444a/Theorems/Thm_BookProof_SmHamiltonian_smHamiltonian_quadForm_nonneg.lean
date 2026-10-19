-- Prove2me | Theorems.Thm_BookProof_SmHamiltonian_smHamiltonian_quadForm_nonneg
-- name    : BookProof.SmHamiltonian.smHamiltonian_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:17:39.540545+00:00
-- url     : https://prove2.me/theorems/7eac28f7-7d96-4c7d-9ec8-2b415b794087
-- title:
--   `BookProof.SmHamiltonian.smHamiltonian_quadForm_nonneg` (P : SmParams) (x : polyGaussCore (d := 163)) : 0 ≤ quadForm (smHamiltonian P) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHamiltonian`.
--
--   `BookProof.SmHamiltonian.smHamiltonian_quadForm_nonneg` (P : SmParams) (x : polyGaussCore (d := 163)) : 0 ≤ quadForm (smHamiltonian P) x
--
--   Formalization note: Lean 4 identifier `BookProof.SmHamiltonian.smHamiltonian_quadForm_nonneg`.

-- Generated from ChapterSmHamiltonian.lean — theorem BookProof.SmHamiltonian.smHamiltonian_quadForm_nonneg
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

theorem BookProof.SmHamiltonian.smHamiltonian_quadForm_nonneg (P : SmParams) (x : polyGaussCore (d := 163)) :
    0 ≤ quadForm (smHamiltonian P) x := by sorry
