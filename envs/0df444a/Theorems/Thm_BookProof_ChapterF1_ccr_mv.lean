-- Prove2me | Theorems.Thm_BookProof_ChapterF1_ccr_mv
-- name    : BookProof.ChapterF1.ccr_mv
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:44:21.750563+00:00
-- url     : https://prove2.me/theorems/68a5555e-5a9c-486d-8ec7-cc7140520ec9
-- title:
--   `BookProof.ChapterF1.ccr_mv` {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℂ) : (MvPolynomial.pderiv i) (MvPolynomial.X j * p) - MvPolynomial.X j * (MvPolynomial.pderiv i) p = (i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF1`.
--
--   `BookProof.ChapterF1.ccr_mv` {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℂ) : (MvPolynomial.pderiv i) (MvPolynomial.X j * p) - MvPolynomial.X j * (MvPolynomial.pderiv i) p = (if i = j then p else 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF1.ccr_mv`.

-- Generated from ChapterF1.lean — theorem BookProof.ChapterF1.ccr_mv
import Mathlib
import Definitions.Def_ChapterF1
open BookProof.ChapterF1


open Polynomial Finset
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF1.ccr_mv {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℂ) :
    (MvPolynomial.pderiv i) (MvPolynomial.X j * p)
      - MvPolynomial.X j * (MvPolynomial.pderiv i) p
      = (if i = j then p else 0) := by sorry
