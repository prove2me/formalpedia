-- Prove2me | Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_hermiteFactor_mul
-- name    : BookProof.GaussCoordCombo.gaussInt_hermiteFactor_mul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:19:39.904878+00:00
-- url     : https://prove2.me/theorems/567c062d-ea6b-4473-9bfa-99112973ef76
-- title:
--   `BookProof.GaussCoordCombo.gaussInt_hermiteFactor_mul` (i : Fin d) (m n : ℕ) {R : MvPolynomial (Fin d) ℂ} (hR : pderiv i R = 0) : gaussInt (hermiteFactor i m * (hermiteFactor i n *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaussCoordCombo`.
--
--   `BookProof.GaussCoordCombo.gaussInt_hermiteFactor_mul` (i : Fin d) (m n : ℕ) {R : MvPolynomial (Fin d) ℂ} (hR : pderiv i R = 0) : gaussInt (hermiteFactor i m * (hermiteFactor i n * R)) = (if m = n then (n.factorial : ℂ) else 0) * gaussInt R
--
--   Formalization note: Lean 4 identifier `BookProof.GaussCoordCombo.gaussInt_hermiteFactor_mul`.

-- Generated from ChapterGaussCoordCombo.lean — theorem BookProof.GaussCoordCombo.gaussInt_hermiteFactor_mul
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.GaussCoordCombo



open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.GaussCoordCombo.gaussInt_hermiteFactor_mul (i : Fin d) (m n : ℕ) {R : MvPolynomial (Fin d) ℂ}
    (hR : pderiv i R = 0) :
    gaussInt (hermiteFactor i m * (hermiteFactor i n * R))
      = (if m = n then (n.factorial : ℂ) else 0) * gaussInt R := by sorry
