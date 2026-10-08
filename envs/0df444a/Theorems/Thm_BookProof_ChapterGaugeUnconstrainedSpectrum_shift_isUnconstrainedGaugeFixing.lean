-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_shift_isUnconstrainedGaugeFixing
-- name    : BookProof.ChapterGaugeUnconstrainedSpectrum.shift_isUnconstrainedGaugeFixing
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:16:12.121976+00:00
-- url     : https://prove2.me/theorems/1782dd87-a0cf-414a-b09d-dde5c5f1f78b
-- title:
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.shift_isUnconstrainedGaugeFixing` : IsUnconstrainedGaugeFixing (fun m : Multiplicative ℤ => permOp (shiftPerm m))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeUnconstrainedSpectrum`.
--
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.shift_isUnconstrainedGaugeFixing` : IsUnconstrainedGaugeFixing (fun m : Multiplicative ℤ => permOp (shiftPerm m))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeUnconstrainedSpectrum.shift_isUnconstrainedGaugeFixing`.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — theorem BookProof.ChapterGaugeUnconstrainedSpectrum.shift_isUnconstrainedGaugeFixing
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum



variable {X : Type*}

variable {G : Type*} [Group G]

theorem BookProof.ChapterGaugeUnconstrainedSpectrum.shift_isUnconstrainedGaugeFixing :
    IsUnconstrainedGaugeFixing (fun m : Multiplicative ℤ => permOp (shiftPerm m)) := by sorry
