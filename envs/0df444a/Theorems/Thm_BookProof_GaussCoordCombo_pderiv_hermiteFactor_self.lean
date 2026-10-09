-- Prove2me | Theorems.Thm_BookProof_GaussCoordCombo_pderiv_hermiteFactor_self
-- name    : BookProof.GaussCoordCombo.pderiv_hermiteFactor_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:18:32.885282+00:00
-- url     : https://prove2.me/theorems/81aad8aa-073e-4a14-af3a-c1155e92d4c3
-- title:
--   `BookProof.GaussCoordCombo.pderiv_hermiteFactor_self` (i : Fin d) (n : ℕ) : pderiv i (hermiteFactor i (n + 1)) = ((n : ℂ) + 1) • hermiteFactor i n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaussCoordCombo`.
--
--   `BookProof.GaussCoordCombo.pderiv_hermiteFactor_self` (i : Fin d) (n : ℕ) : pderiv i (hermiteFactor i (n + 1)) = ((n : ℂ) + 1) • hermiteFactor i n
--
--   Formalization note: Lean 4 identifier `BookProof.GaussCoordCombo.pderiv_hermiteFactor_self`.

-- Generated from ChapterGaussCoordCombo.lean — theorem BookProof.GaussCoordCombo.pderiv_hermiteFactor_self
import Mathlib
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.GaussCoordCombo



open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.GaussCoordCombo.pderiv_hermiteFactor_self (i : Fin d) (n : ℕ) :
    pderiv i (hermiteFactor i (n + 1)) = ((n : ℂ) + 1) • hermiteFactor i n := by sorry
