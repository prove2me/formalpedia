-- Prove2me | Theorems.Thm_BookProof_GaussCoordCombo_pderiv_coordCombo_of_ne
-- name    : BookProof.GaussCoordCombo.pderiv_coordCombo_of_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:19:50.063983+00:00
-- url     : https://prove2.me/theorems/aa3d99b4-1c64-40d5-b1ef-3c75162b7477
-- title:
--   `BookProof.GaussCoordCombo.pderiv_coordCombo_of_ne` {i j : Fin d} (h : j ≠ i) (c : ℕ → ℝ) (p K : ℕ) : pderiv j (coordCombo i c p K) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaussCoordCombo`.
--
--   `BookProof.GaussCoordCombo.pderiv_coordCombo_of_ne` {i j : Fin d} (h : j ≠ i) (c : ℕ → ℝ) (p K : ℕ) : pderiv j (coordCombo i c p K) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.GaussCoordCombo.pderiv_coordCombo_of_ne`.

-- Generated from ChapterGaussCoordCombo.lean — theorem BookProof.GaussCoordCombo.pderiv_coordCombo_of_ne
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.GaussCoordCombo



open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.GaussCoordCombo.pderiv_coordCombo_of_ne {i j : Fin d} (h : j ≠ i) (c : ℕ → ℝ) (p K : ℕ) :
    pderiv j (coordCombo i c p K) = 0 := by sorry
