-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_shift_full_spectrum_vs_observable_spectrum
-- name    : BookProof.ChapterGaugeUnconstrainedSpectrum.shift_full_spectrum_vs_observable_spectrum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:17:57.018756+00:00
-- url     : https://prove2.me/theorems/a1a61adb-1be8-4ff5-aaf8-2fb605adce50
-- title:
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.shift_full_spectrum_vs_observable_spectrum` : IsUnconstrainedGaugeFixing (fun m : Multiplicative ℤ => permOp (shiftPerm m)) ∧ constrain
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeUnconstrainedSpectrum`.
--
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.shift_full_spectrum_vs_observable_spectrum` : IsUnconstrainedGaugeFixing (fun m : Multiplicative ℤ => permOp (shiftPerm m)) ∧ constrainedSpectrum (fun m : Multiplicative ℤ => permOp (shiftPerm m)) = (Set.univ : Set ℤ) ∧ (Set.univ : Set ℤ).Infinite ∧ Subsingleton (observableSpectrum shiftPerm)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeUnconstrainedSpectrum.shift_full_spectrum_vs_observable_spectrum`.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — theorem BookProof.ChapterGaugeUnconstrainedSpectrum.shift_full_spectrum_vs_observable_spectrum
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum



variable {X : Type*}

variable {G : Type*} [Group G]

theorem BookProof.ChapterGaugeUnconstrainedSpectrum.shift_full_spectrum_vs_observable_spectrum :
    IsUnconstrainedGaugeFixing (fun m : Multiplicative ℤ => permOp (shiftPerm m)) ∧
      constrainedSpectrum (fun m : Multiplicative ℤ => permOp (shiftPerm m)) =
        (Set.univ : Set ℤ) ∧
      (Set.univ : Set ℤ).Infinite ∧
      Subsingleton (observableSpectrum shiftPerm) := by sorry
