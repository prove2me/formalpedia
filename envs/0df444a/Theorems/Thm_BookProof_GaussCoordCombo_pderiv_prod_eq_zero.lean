-- Prove2me | Theorems.Thm_BookProof_GaussCoordCombo_pderiv_prod_eq_zero
-- name    : BookProof.GaussCoordCombo.pderiv_prod_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:20:29.894077+00:00
-- url     : https://prove2.me/theorems/31b3a612-a107-45ed-ac43-28aeee35af13
-- title:
--   `BookProof.GaussCoordCombo.pderiv_prod_eq_zero` {S : Finset (Fin d)} {W : Fin d → MvPolynomial (Fin d) ℂ} {i : Fin d} (h : ∀ j ∈ S, pderiv i (W j) = 0) : pderiv i (∏ j ∈ S, W j) =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaussCoordCombo`.
--
--   `BookProof.GaussCoordCombo.pderiv_prod_eq_zero` {S : Finset (Fin d)} {W : Fin d → MvPolynomial (Fin d) ℂ} {i : Fin d} (h : ∀ j ∈ S, pderiv i (W j) = 0) : pderiv i (∏ j ∈ S, W j) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.GaussCoordCombo.pderiv_prod_eq_zero`.

-- Generated from ChapterGaussCoordCombo.lean — theorem BookProof.GaussCoordCombo.pderiv_prod_eq_zero
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.GaussCoordCombo



open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.GaussCoordCombo.pderiv_prod_eq_zero {S : Finset (Fin d)} {W : Fin d → MvPolynomial (Fin d) ℂ}
    {i : Fin d} (h : ∀ j ∈ S, pderiv i (W j) = 0) : pderiv i (∏ j ∈ S, W j) = 0 := by sorry
