-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_isUnconstrained_of_faithful
-- name    : BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_faithful
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:18:02.48853+00:00
-- url     : https://prove2.me/theorems/94643df6-e88a-4c76-b3e5-371d1adb1148
-- title:
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_faithful` {ρ : G →* Equiv.Perm X} (hρ : Function.Injective ρ) : IsUnconstrainedGaugeFixing (fun g => permOp (ρ g))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeUnconstrainedSpectrum`.
--
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_faithful` {ρ : G →* Equiv.Perm X} (hρ : Function.Injective ρ) : IsUnconstrainedGaugeFixing (fun g => permOp (ρ g))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_faithful`.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — theorem BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_faithful
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum



variable {X : Type*}

variable {G : Type*} [Group G]

theorem BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_faithful {ρ : G →* Equiv.Perm X}
    (hρ : Function.Injective ρ) :
    IsUnconstrainedGaugeFixing (fun g => permOp (ρ g)) := by sorry
