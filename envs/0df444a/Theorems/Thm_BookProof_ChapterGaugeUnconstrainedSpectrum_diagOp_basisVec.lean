-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_diagOp_basisVec
-- name    : BookProof.ChapterGaugeUnconstrainedSpectrum.diagOp_basisVec
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:15:24.017277+00:00
-- url     : https://prove2.me/theorems/3c1b9780-0bd7-4132-9b1e-570089f9fc24
-- title:
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.diagOp_basisVec` [DecidableEq X] (d : X → ℂ) (y : X) : diagOp d (basisVec y) = d y • basisVec y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeUnconstrainedSpectrum`.
--
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.diagOp_basisVec` [DecidableEq X] (d : X → ℂ) (y : X) : diagOp d (basisVec y) = d y • basisVec y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeUnconstrainedSpectrum.diagOp_basisVec`.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — theorem BookProof.ChapterGaugeUnconstrainedSpectrum.diagOp_basisVec
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterE4
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterE4
open BookProof.ChapterGaugeUnconstrainedSpectrum



variable {X : Type*}

theorem BookProof.ChapterGaugeUnconstrainedSpectrum.diagOp_basisVec [DecidableEq X] (d : X → ℂ) (y : X) :
    diagOp d (basisVec y) = d y • basisVec y := by sorry
