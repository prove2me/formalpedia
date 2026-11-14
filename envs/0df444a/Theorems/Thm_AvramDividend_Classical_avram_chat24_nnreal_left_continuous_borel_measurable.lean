-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_nnreal_left_continuous_borel_measurable
-- name    : AvramDividend.Classical.avram_chat24_nnreal_left_continuous_borel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T18:57:37.153205+00:00
-- url     : https://prove2.me/theorems/6d1c89b0-a333-4b7e-bc65-2af9b106bde4
-- title:
--   Borel measurability of left-continuous functions on nonnegative reals
-- statement:
--   A real-valued function on the nonnegative reals that is continuous from the left at every point is Borel measurable. This isolates the measurable-grid approximation argument for parent e48a1e4f-d06c-47e4-abaf-889f3ce118a6. For that parent, set g = Function.leftLim f; continuousWithinAt_leftLim_Iic and the assumed strict left limits give hg, including the minimum 0. The child is independent of its parent, so no dependency cycle is introduced. A public declaration is required because the authoritative parent e48a1e4f-d06c-47e4-abaf-889f3ce118a6 is public and guarded preflight correctly forbids its importing a private helper. Private predecessor 7c724aa8-ce69-46f2-b0f2-43fa84193482 cannot supply that public reduction. The mathematical statement is unchanged; no parent dependency or cycle is introduced.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal Topology

theorem AvramDividend.Classical.avram_chat24_nnreal_left_continuous_borel_measurable
    (g : ℝ≥0 → ℝ) (hg : ∀ t : ℝ≥0, ContinuousWithinAt g (Iic t) t) :
    Measurable g := by sorry
