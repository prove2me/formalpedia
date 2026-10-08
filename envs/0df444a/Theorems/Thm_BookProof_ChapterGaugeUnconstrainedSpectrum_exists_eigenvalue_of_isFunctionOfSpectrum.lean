-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_exists_eigenvalue_of_isFunctionOfSpectrum
-- name    : BookProof.ChapterGaugeUnconstrainedSpectrum.exists_eigenvalue_of_isFunctionOfSpectrum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:15:24.820213+00:00
-- url     : https://prove2.me/theorems/f2c5b702-b9dc-4597-aca0-1b2cc4e62bd3
-- title:
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.exists_eigenvalue_of_isFunctionOfSpectrum` [DecidableEq X] {T : Op X} (hT : IsFunctionOfSpectrum T) (y : X) : ∃ c : ℂ, T (basisVec y) =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeUnconstrainedSpectrum`.
--
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.exists_eigenvalue_of_isFunctionOfSpectrum` [DecidableEq X] {T : Op X} (hT : IsFunctionOfSpectrum T) (y : X) : ∃ c : ℂ, T (basisVec y) = c • basisVec y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeUnconstrainedSpectrum.exists_eigenvalue_of_isFunctionOfSpectrum`.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — theorem BookProof.ChapterGaugeUnconstrainedSpectrum.exists_eigenvalue_of_isFunctionOfSpectrum
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterE4
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterE4
open BookProof.ChapterGaugeUnconstrainedSpectrum



variable {X : Type*}

theorem BookProof.ChapterGaugeUnconstrainedSpectrum.exists_eigenvalue_of_isFunctionOfSpectrum [DecidableEq X] {T : Op X}
    (hT : IsFunctionOfSpectrum T) (y : X) :
    ∃ c : ℂ, T (basisVec y) = c • basisVec y := by sorry
