-- Prove2me | Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_coordCombo_sq
-- name    : BookProof.GaussCoordCombo.gaussInt_coordCombo_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:20:07.269646+00:00
-- url     : https://prove2.me/theorems/555f5ea7-0682-4a23-8ca9-7859db8899ac
-- title:
--   `BookProof.GaussCoordCombo.gaussInt_coordCombo_sq` (i : Fin d) (c : ℕ → ℝ) (p K : ℕ) {R : MvPolynomial (Fin d) ℂ} (hR : pderiv i R = 0) : gaussInt (coordCombo i c p K * (coordCombo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaussCoordCombo`.
--
--   `BookProof.GaussCoordCombo.gaussInt_coordCombo_sq` (i : Fin d) (c : ℕ → ℝ) (p K : ℕ) {R : MvPolynomial (Fin d) ℂ} (hR : pderiv i R = 0) : gaussInt (coordCombo i c p K * (coordCombo i c p K * R)) = ((coordComboSum c p K : ℝ) : ℂ) * gaussInt R
--
--   Formalization note: Lean 4 identifier `BookProof.GaussCoordCombo.gaussInt_coordCombo_sq`.

-- Generated from ChapterGaussCoordCombo.lean — theorem BookProof.GaussCoordCombo.gaussInt_coordCombo_sq
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.GaussCoordCombo



open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.GaussCoordCombo.gaussInt_coordCombo_sq (i : Fin d) (c : ℕ → ℝ) (p K : ℕ)
    {R : MvPolynomial (Fin d) ℂ} (hR : pderiv i R = 0) :
    gaussInt (coordCombo i c p K * (coordCombo i c p K * R))
      = ((coordComboSum c p K : ℝ) : ℂ) * gaussInt R := by sorry
