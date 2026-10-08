-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_permOp_basisVec
-- name    : BookProof.ChapterGaugeUnconstrainedSpectrum.permOp_basisVec
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:15:32.046704+00:00
-- url     : https://prove2.me/theorems/e179f2a2-2d7c-4f63-8e7d-a75fbbb081dc
-- title:
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.permOp_basisVec` [DecidableEq X] (σ : Equiv.Perm X) (y : X) : permOp σ (basisVec y) = basisVec (σ y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeUnconstrainedSpectrum`.
--
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.permOp_basisVec` [DecidableEq X] (σ : Equiv.Perm X) (y : X) : permOp σ (basisVec y) = basisVec (σ y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeUnconstrainedSpectrum.permOp_basisVec`.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — theorem BookProof.ChapterGaugeUnconstrainedSpectrum.permOp_basisVec
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterE4
open BookProof.ChapterE4
open BookProof.ChapterGaugeUnconstrainedSpectrum



variable {X : Type*}

theorem BookProof.ChapterGaugeUnconstrainedSpectrum.permOp_basisVec [DecidableEq X] (σ : Equiv.Perm X) (y : X) :
    permOp σ (basisVec y) = basisVec (σ y) := by sorry
