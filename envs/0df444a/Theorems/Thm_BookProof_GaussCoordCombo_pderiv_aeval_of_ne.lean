-- Prove2me | Theorems.Thm_BookProof_GaussCoordCombo_pderiv_aeval_of_ne
-- name    : BookProof.GaussCoordCombo.pderiv_aeval_of_ne
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:18:28.497926+00:00
-- url     : https://prove2.me/theorems/66891c22-5049-4a76-a739-07ce79e2261b
-- title:
--   `BookProof.GaussCoordCombo.pderiv_aeval_of_ne` {i j : Fin d} (h : j ≠ i) (f : Polynomial ℂ) : pderiv j (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) f) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaussCoordCombo`.
--
--   `BookProof.GaussCoordCombo.pderiv_aeval_of_ne` {i j : Fin d} (h : j ≠ i) (f : Polynomial ℂ) : pderiv j (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) f) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.GaussCoordCombo.pderiv_aeval_of_ne`.

-- Generated from ChapterGaussCoordCombo.lean — theorem BookProof.GaussCoordCombo.pderiv_aeval_of_ne
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.GaussCoordCombo



open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.GaussCoordCombo.pderiv_aeval_of_ne {i j : Fin d} (h : j ≠ i) (f : Polynomial ℂ) :
    pderiv j (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) f) = 0 := by sorry
