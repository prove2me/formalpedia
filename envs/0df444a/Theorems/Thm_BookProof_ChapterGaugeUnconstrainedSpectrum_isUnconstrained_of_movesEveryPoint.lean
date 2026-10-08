-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_isUnconstrained_of_movesEveryPoint
-- name    : BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_movesEveryPoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:16:09.088076+00:00
-- url     : https://prove2.me/theorems/c1d42069-75df-424b-bca0-69bde677f772
-- title:
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_movesEveryPoint` [Nonempty X] {ρ : G →* Equiv.Perm X} (hmoves : ∀ g : G, g ≠ 1 → ∀ x : X, ρ g x ≠ x) : IsUnconstrain
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeUnconstrainedSpectrum`.
--
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_movesEveryPoint` [Nonempty X] {ρ : G →* Equiv.Perm X} (hmoves : ∀ g : G, g ≠ 1 → ∀ x : X, ρ g x ≠ x) : IsUnconstrainedGaugeFixing (fun g => permOp (ρ g))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_movesEveryPoint`.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — theorem BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_movesEveryPoint
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum



variable {X : Type*}

variable {G : Type*} [Group G]

theorem BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_movesEveryPoint [Nonempty X]
    {ρ : G →* Equiv.Perm X} (hmoves : ∀ g : G, g ≠ 1 → ∀ x : X, ρ g x ≠ x) :
    IsUnconstrainedGaugeFixing (fun g => permOp (ρ g)) := by sorry
