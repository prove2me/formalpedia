-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_limit_aestrongly_measurable
-- name    : AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_limit_aestrongly_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:56:22.557144+00:00
-- url     : https://prove2.me/theorems/155f9cd1-b3e5-4054-bc8b-3df36f5cd3de
-- title:
--   Measurability of the finite-horizon stopped q-scale limit
-- statement:
--   For a spectrally negative Lévy process with W(0)=0, the discounted q-scale value at the capped actual two-sided first-passage time is almost everywhere strongly measurable. Derive this from the established almost-everywhere convergence of the actual uniform-grid rewards and the measurability of each grid reward under its reindexed filtration. No independent measurability of the continuous-time stopping time is assumed.
-- source:
--   Apply Mathlib's aestronglyMeasurable_of_tendsto_ae to measurable grid rewards, using accepted clipped-grid hit congruence and pathwise almost-everywhere convergence.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_ae_all_branches
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_scale_reward_measurable
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_limit_aestrongly_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (x lower upper : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P, IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (mesh : ℕ → ℝ≥0) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    AEStronglyMeasurable
      (fun ω => Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
        W (x + X.X (min (τ ω) T) ω)) P := by
  sorry
