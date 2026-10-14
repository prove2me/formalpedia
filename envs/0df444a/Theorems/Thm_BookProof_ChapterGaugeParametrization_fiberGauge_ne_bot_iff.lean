-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeParametrization_fiberGauge_ne_bot_iff
-- name    : BookProof.ChapterGaugeParametrization.fiberGauge_ne_bot_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:46:38.328911+00:00
-- url     : https://prove2.me/theorems/067abb52-07db-497f-8c1a-431a8e1b02fb
-- title:
--   `BookProof.ChapterGaugeParametrization.fiberGauge_ne_bot_iff` (π : X → Y) : fiberGauge π ≠ ⊥ ↔ ¬ Function.Injective π
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeParametrization`.
--
--   `BookProof.ChapterGaugeParametrization.fiberGauge_ne_bot_iff` (π : X → Y) : fiberGauge π ≠ ⊥ ↔ ¬ Function.Injective π
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeParametrization.fiberGauge_ne_bot_iff`.

-- Generated from ChapterGaugeParametrization.lean — theorem BookProof.ChapterGaugeParametrization.fiberGauge_ne_bot_iff
import Definitions.Def_ChapterGaugeIncompleteFixing
import Mathlib
import Definitions.Def_ChapterGaugeParametrization
open BookProof.ChapterGaugeParametrization



open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

theorem BookProof.ChapterGaugeParametrization.fiberGauge_ne_bot_iff (π : X → Y) :
    fiberGauge π ≠ ⊥ ↔ ¬ Function.Injective π := by sorry
