-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeParametrization_isCompleteGaugeFixing_prime_iff_injOn
-- name    : BookProof.ChapterGaugeParametrization.isCompleteGaugeFixing_prime_iff_injOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T11:16:04.364171+00:00
-- url     : https://prove2.me/theorems/a9a45512-8cb7-4e19-b1e0-4b7b7b8a93eb
-- title:
--   BookProof.ChapterGaugeParametrization.isCompleteGaugeFixing'_iff_injOn
-- statement:
--   BookProof.ChapterGaugeParametrization.isCompleteGaugeFixing'_iff_injOn

-- Generated from ChapterGaugeParametrization.lean — theorem BookProof.ChapterGaugeParametrization.isCompleteGaugeFixing'_iff_injOn
import Mathlib
import Definitions.Def_ChapterGaugeParametrization
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeParametrization



open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

theorem BookProof.ChapterGaugeParametrization.isCompleteGaugeFixing_prime_iff_injOn (π : X → Y) (S : Set X) :
    IsCompleteGaugeFixing' (fiberGauge π) S ↔ Set.InjOn π S := by sorry
