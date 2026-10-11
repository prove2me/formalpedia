-- Prove2me | Theorems.Thm_BookProof_SmHamiltonian_realCoeff_C_real
-- name    : BookProof.SmHamiltonian.realCoeff_C_real
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:58:06.804478+00:00
-- url     : https://prove2.me/theorems/6ed490fc-b42e-4e5d-b8f5-f3f2d4b05025
-- title:
--   `BookProof.SmHamiltonian.realCoeff_C_real` {d : ℕ} (t : ℝ) : RealCoeff (C ((t : ℝ) : ℂ) : MvPolynomial (Fin d) ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmHamiltonian`.
--
--   `BookProof.SmHamiltonian.realCoeff_C_real` {d : ℕ} (t : ℝ) : RealCoeff (C ((t : ℝ) : ℂ) : MvPolynomial (Fin d) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmHamiltonian.realCoeff_C_real`.

-- Generated from ChapterSmHamiltonian.lean — theorem BookProof.SmHamiltonian.realCoeff_C_real
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

theorem BookProof.SmHamiltonian.realCoeff_C_real {d : ℕ} (t : ℝ) :
    RealCoeff (C ((t : ℝ) : ℂ) : MvPolynomial (Fin d) ℂ) := by sorry
