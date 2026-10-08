-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_isPhysicalFunction_iff_factors
-- name    : BookProof.ChapterGaugeUnconstrainedSpectrum.isPhysicalFunction_iff_factors
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:16:49.923982+00:00
-- url     : https://prove2.me/theorems/c0788a03-70fd-4479-98ea-8cf7350be3be
-- title:
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.isPhysicalFunction_iff_factors` (ρ : G →* Equiv.Perm X) (d : X → ℂ) : IsPhysicalFunction ρ d ↔ ∃ D : observableSpectrum ρ → ℂ, ∀ x : X,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeUnconstrainedSpectrum`.
--
--   `BookProof.ChapterGaugeUnconstrainedSpectrum.isPhysicalFunction_iff_factors` (ρ : G →* Equiv.Perm X) (d : X → ℂ) : IsPhysicalFunction ρ d ↔ ∃ D : observableSpectrum ρ → ℂ, ∀ x : X, d x = D (Quotient.mk (orbitSetoid ρ) x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeUnconstrainedSpectrum.isPhysicalFunction_iff_factors`.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — theorem BookProof.ChapterGaugeUnconstrainedSpectrum.isPhysicalFunction_iff_factors
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterGaugeUnconstrainedSpectrum



variable {X : Type*}

variable {G : Type*} [Group G]

theorem BookProof.ChapterGaugeUnconstrainedSpectrum.isPhysicalFunction_iff_factors (ρ : G →* Equiv.Perm X) (d : X → ℂ) :
    IsPhysicalFunction ρ d ↔
      ∃ D : observableSpectrum ρ → ℂ, ∀ x : X, d x = D (Quotient.mk (orbitSetoid ρ) x) := by sorry
