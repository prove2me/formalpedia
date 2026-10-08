-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeParametrization_isComprehensiveGaugeFixing_iff_surjOn
-- name    : BookProof.ChapterGaugeParametrization.isComprehensiveGaugeFixing_iff_surjOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T11:16:11.820681+00:00
-- url     : https://prove2.me/theorems/72865a5d-1456-452c-8fcb-242ee55aafcf
-- title:
--   `BookProof.ChapterGaugeParametrization.isComprehensiveGaugeFixing_iff_surjOn` (π : X → Y) (S : Set X) : IsComprehensiveGaugeFixing (fiberGauge π) S ↔ ∀ x : X, ∃ s ∈ S, π s = π x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeParametrization`.
--
--   `BookProof.ChapterGaugeParametrization.isComprehensiveGaugeFixing_iff_surjOn` (π : X → Y) (S : Set X) : IsComprehensiveGaugeFixing (fiberGauge π) S ↔ ∀ x : X, ∃ s ∈ S, π s = π x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeParametrization.isComprehensiveGaugeFixing_iff_surjOn`.

-- Generated from ChapterGaugeParametrization.lean — theorem BookProof.ChapterGaugeParametrization.isComprehensiveGaugeFixing_iff_surjOn
import Mathlib
import Definitions.Def_ChapterGaugeParametrization
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeParametrization



open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

theorem BookProof.ChapterGaugeParametrization.isComprehensiveGaugeFixing_iff_surjOn (π : X → Y) (S : Set X) :
    IsComprehensiveGaugeFixing (fiberGauge π) S ↔ ∀ x : X, ∃ s ∈ S, π s = π x := by sorry
