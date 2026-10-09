-- Prove2me | Theorems.Thm_BookProof_GaussCoordCombo_gaussInt_prod_coordFactor
-- name    : BookProof.GaussCoordCombo.gaussInt_prod_coordFactor
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:20:37.819767+00:00
-- url     : https://prove2.me/theorems/b1cf2e29-4833-4d0b-94cf-5d634bddd6fa
-- title:
--   `BookProof.GaussCoordCombo.gaussInt_prod_coordFactor` {S : Finset (Fin d)} {W : Fin d → MvPolynomial (Fin d) ℂ} {s : Fin d → ℝ} (hW : ∀ j ∈ S, CoordFactor j (W j) (s j)) {R : MvPol
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaussCoordCombo`.
--
--   `BookProof.GaussCoordCombo.gaussInt_prod_coordFactor` {S : Finset (Fin d)} {W : Fin d → MvPolynomial (Fin d) ℂ} {s : Fin d → ℝ} (hW : ∀ j ∈ S, CoordFactor j (W j) (s j)) {R : MvPolynomial (Fin d) ℂ} (hR : ∀ j ∈ S, pderiv j R = 0) : gaussInt ((∏ j ∈ S, W j) * ((∏ j ∈ S, W j) * R)) = ((∏ j ∈ S, s j : ℝ) : ℂ) * gaussInt R
--
--   Formalization note: Lean 4 identifier `BookProof.GaussCoordCombo.gaussInt_prod_coordFactor`.

-- Generated from ChapterGaussCoordCombo.lean — theorem BookProof.GaussCoordCombo.gaussInt_prod_coordFactor
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.GaussCoordCombo



open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.GaussCoordCombo.gaussInt_prod_coordFactor {S : Finset (Fin d)} {W : Fin d → MvPolynomial (Fin d) ℂ}
    {s : Fin d → ℝ} (hW : ∀ j ∈ S, CoordFactor j (W j) (s j))
    {R : MvPolynomial (Fin d) ℂ} (hR : ∀ j ∈ S, pderiv j R = 0) :
    gaussInt ((∏ j ∈ S, W j) * ((∏ j ∈ S, W j) * R))
      = ((∏ j ∈ S, s j : ℝ) : ℂ) * gaussInt R := by sorry
