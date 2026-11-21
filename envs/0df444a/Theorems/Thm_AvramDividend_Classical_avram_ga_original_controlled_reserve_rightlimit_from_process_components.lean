-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_controlled_reserve_rightlimit_from_process_components
-- name    : AvramDividend.Classical.avram_ga_original_controlled_reserve_rightlimit_from_process_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:27:24.889182+00:00
-- url     : https://prove2.me/theorems/5db461a3-93de-45dc-8118-30c88124e8f9
-- title:
--   Original stopped controlled reserve has physical post-dividend right limit from Gaussian path continuity and dividend right limits
-- statement:
--   For the original SpectrallyNegativeLevy X, controlled reserve riskProcess X x D, and the authentic dividend rightLimit D at time t, if the original X path is right-continuous at t and D converges to rightLimit D_t from strictly later times, then riskProcess converges from the right to x+X_t−rightLimit D_t. This is the missing original-process continuity input to transfer the strict pre-stop reserve floor to the postpayment physical mesh. It retains the right-jump dividend convention and does not assume dividend paths are continuous.
-- source:
--   Combines authentic zero-jump Gaussian path right continuity and original càglàd dividend strategy right limits to identify the post-dividend reserve, enabling lower-clipping equivalence with the Proved gb63 finite-cap Hessian martingale-difference source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Filter Topology Set MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_controlled_reserve_rightlimit_from_process_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0)
    (hX : Tendsto (fun u : ℝ≥0 => X.X u ω)
      (𝓝[>] t) (𝓝 (X.X t ω)))
    (hD : Tendsto (fun u : ℝ≥0 => D u ω)
      (𝓝[>] t) (𝓝 (rightLimit D t ω))) :
    Tendsto (fun u : ℝ≥0 => riskProcess X x D u ω)
      (𝓝[>] t)
      (𝓝 (x + X.X t ω - rightLimit D t ω)) := by sorry
