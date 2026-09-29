-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_observable_propagation
-- name    : BookProof.SirkFinitePrecision.observable_propagation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:50:49.415333+00:00
-- url     : https://prove2.me/theorems/f307ddcb-aea9-4be3-9bdc-a52b70acedfd
-- title:
--   T4, Cauchy–Schwarz propagation.** Two states that are close in norm give close expectations of a bounded observable
-- statement:
--   **T4, Cauchy–Schwarz propagation.**  Two states that are close in norm give close
--   expectations of a bounded observable.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.observable_propagation` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 311–334.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L311-L334

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.observable_propagation
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.observable_propagation {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (O : F →L[ℂ] F) (u w : F) :
    |(inner ℂ u (O u)).re - (inner ℂ w (O w)).re| ≤ ‖O‖ * (‖u‖ + ‖w‖) * ‖u - w‖ := by sorry
