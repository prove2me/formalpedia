-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeParametrization_isPhysicalObservable_iff_factors_through
-- name    : BookProof.ChapterGaugeParametrization.isPhysicalObservable_iff_factors_through
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T11:16:06.460092+00:00
-- url     : https://prove2.me/theorems/e521b89e-80c7-4067-bf2e-a98d981a277d
-- title:
--   `BookProof.ChapterGaugeParametrization.isPhysicalObservable_iff_factors_through` (π : X → Y) (f : X → ℝ) : IsPhysicalObservable (fiberGauge π) f ↔ ∃ F : Y → ℝ, ∀ x, f x = F (π x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeParametrization`.
--
--   `BookProof.ChapterGaugeParametrization.isPhysicalObservable_iff_factors_through` (π : X → Y) (f : X → ℝ) : IsPhysicalObservable (fiberGauge π) f ↔ ∃ F : Y → ℝ, ∀ x, f x = F (π x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeParametrization.isPhysicalObservable_iff_factors_through`.

-- Generated from ChapterGaugeParametrization.lean — theorem BookProof.ChapterGaugeParametrization.isPhysicalObservable_iff_factors_through
import Mathlib
import Definitions.Def_ChapterGaugeParametrization
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeParametrization



open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

theorem BookProof.ChapterGaugeParametrization.isPhysicalObservable_iff_factors_through (π : X → Y) (f : X → ℝ) :
    IsPhysicalObservable (fiberGauge π) f ↔ ∃ F : Y → ℝ, ∀ x, f x = F (π x) := by sorry
