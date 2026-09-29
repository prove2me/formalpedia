-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_observable_propagation_band
-- name    : BookProof.SirkFinitePrecision.observable_propagation_band
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:04:07.168968+00:00
-- url     : https://prove2.me/theorems/c2edf457-7068-4cd8-8919-19736ca3db8d
-- title:
--   The `2‖O‖ · R · band` form of T4 used by the kernel's `certify`: if both states are bounded by `R` and differ by at most `band`, the expectations differ by at most `2‖O‖ · R · band`
-- statement:
--   The `2‖O‖ · R · band` form of T4 used by the kernel's `certify`: if both states
--   are bounded by `R` and differ by at most `band`, the expectations differ by at most
--   `2‖O‖ · R · band`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.observable_propagation_band` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 336–351.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L336-L351

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.observable_propagation_band
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.observable_propagation_band {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (O : F →L[ℂ] F) (u w : F) {R band : ℝ}
    (hu : ‖u‖ ≤ R) (hw : ‖w‖ ≤ R) (hband : ‖u - w‖ ≤ band) :
    |(inner ℂ u (O u)).re - (inner ℂ w (O w)).re| ≤ 2 * ‖O‖ * R * band := by sorry
