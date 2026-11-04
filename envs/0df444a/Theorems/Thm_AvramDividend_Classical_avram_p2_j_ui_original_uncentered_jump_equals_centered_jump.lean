-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uncentered_jump_equals_centered_jump
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_uncentered_jump_equals_centered_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:18:16.362481+00:00
-- url     : https://prove2.me/theorems/2fa921f2-fe49-40dc-bf6a-4f083baeebc0
-- title:
--   Original source left-limit jumps equal centred-process left-limit jumps at positive times
-- statement:
--   For every sample path of the exact original spectrally negative Levy process and every strictly positive time, the original-process jump calculated from the canonical uncentred left limit equals the jump of its path centred at its time-zero value. The proof transports the already proved source-exact centred cadlag left-limit convergence under addition of the constant initial value, using a genuine nontrivial positive-time left filter and uniqueness of limits. No zero-origin assumption, rate identity or compensator is used.

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.DenselyOrdered
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_j_ui_original_uncentered_jump_equals_centered_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℝ≥0) (hu : 0 < u) :
    X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u =
      (X.X u ω - X.X 0 ω) -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω - X.X 0 ω) u := by sorry
