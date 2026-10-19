-- Prove2me | Theorems.Thm_BookProof_SmHamiltonian_smHamiltonian_quadForm
-- name    : BookProof.SmHamiltonian.smHamiltonian_quadForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:09:13.449081+00:00
-- url     : https://prove2.me/theorems/4cfb990e-1ca6-4d50-9f2d-39f377e4f993
-- title:
--   `BookProof.SmHamiltonian.smHamiltonian_quadForm` (P : SmParams) (x : polyGaussCore (d := 163)) : quadForm (smHamiltonian P) x = 1 / 2 * (∑ m, ‖((smPi m x : polyGaussCore (d := 163)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHamiltonian`.
--
--   `BookProof.SmHamiltonian.smHamiltonian_quadForm` (P : SmParams) (x : polyGaussCore (d := 163)) : quadForm (smHamiltonian P) x = 1 / 2 * (∑ m, ‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2) + 1 / 2 * ∑ r, ‖((smField P r x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.SmHamiltonian.smHamiltonian_quadForm`.

-- Generated from ChapterSmHamiltonian.lean — theorem BookProof.SmHamiltonian.smHamiltonian_quadForm
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

theorem BookProof.SmHamiltonian.smHamiltonian_quadForm (P : SmParams) (x : polyGaussCore (d := 163)) :
    quadForm (smHamiltonian P) x
      = 1 / 2 * (∑ m, ‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2)
        + 1 / 2 * ∑ r, ‖((smField P r x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by sorry
