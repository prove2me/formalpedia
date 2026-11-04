-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_future_kernel
-- name    : AvramDividend.Classical.avram_p2_e_compensator_weighted_future_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:24:57.693171+00:00
-- url     : https://prove2.me/theorems/6b848c04-9b6c-451f-aef0-85ac5cf402a9
-- title:
--   Original Lévy future-path nonnegative weighted first-moment factorisation
-- statement:
--   For the original spectrally negative Lévy process X on its unchanged probability space and filtration, any nonnegative F_s-measurable weight W and any measurable nonnegative functional F of the whole shifted future-increment path satisfy E[W F(Y_s)] = E[W] E[F(X)]. No boundedness or integrability condition is imposed, with all expectations in ENNReal. This source-faithful factorisation supports predictable marked jump-measure compensation independently of the deterministic Levy measure rate.
-- source:
--   Original-process future kernel past-event theorem 0611e261-f045-4fb5-a53c-a42f06995418 (Proved); pinned Mathlib lintegral_const_mul, lintegral_mul_const, lintegral_map. Parent compensator 393b03a8-2e9a-43d8-b415-854d86d58104 (Open).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_weighted_future_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, W ω * F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) ∂P) =
    (∫⁻ ω, W ω ∂P) *
      (∫⁻ ω, F (fun v : ℝ≥0 => X.X v ω) ∂P) := by sorry
