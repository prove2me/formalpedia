-- Prove2me | Theorems.Thm_BookProof_GaussCoordCombo_pderiv_aeval_self
-- name    : BookProof.GaussCoordCombo.pderiv_aeval_self
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:18:09.452142+00:00
-- url     : https://prove2.me/theorems/dfc4d892-8a8d-45f6-bc0b-a19a8c3c44b8
-- title:
--   `BookProof.GaussCoordCombo.pderiv_aeval_self` (i : Fin d) (f : Polynomial ℂ) : pderiv i (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) f) = Polynomial.aeval (X i : MvPolynomial (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaussCoordCombo`.
--
--   `BookProof.GaussCoordCombo.pderiv_aeval_self` (i : Fin d) (f : Polynomial ℂ) : pderiv i (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) f) = Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) (Polynomial.derivative f)
--
--   Formalization note: Lean 4 identifier `BookProof.GaussCoordCombo.pderiv_aeval_self`.

-- Generated from ChapterGaussCoordCombo.lean — theorem BookProof.GaussCoordCombo.pderiv_aeval_self
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.GaussCoordCombo



open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.GaussCoordCombo.pderiv_aeval_self (i : Fin d) (f : Polynomial ℂ) :
    pderiv i (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) f)
      = Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) (Polynomial.derivative f) := by sorry
