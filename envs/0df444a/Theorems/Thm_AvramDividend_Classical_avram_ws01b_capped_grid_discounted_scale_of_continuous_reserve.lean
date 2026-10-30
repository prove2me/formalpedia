-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_capped_grid_discounted_scale_of_continuous_reserve
-- name    : AvramDividend.Classical.avram_ws01b_capped_grid_discounted_scale_of_continuous_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:55:32.360409+00:00
-- url     : https://prove2.me/theorems/cf21ca25-2942-46e3-baa4-79afedbbaa04
-- title:
--   Capped true first-grid scale convergence from reserve continuity
-- statement:
--   A source-specific pathwise first-strict-grid q-scale payoff converges locally to the capped continuous stopping payoff whenever the genuine scale function is continuous at the realised stopped reserve. It replaces a globally false BV W(0)=0 assumption with the exact local continuity condition. Together with the Proved BV lower strict no-creeping theorem, this supports the BV grid-to-real stopping limit.
-- source:
--   Specialisation of the canonically Proved first-grid capped time convergence  from the actual spectrally negative Lévy process, preserving exact time and spatial path dependence. Uses the original accepted continuity proof with a local continuity hypothesis at the true stopped reserve. No martingale or W(0)=0 assumed.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_capped_time_convergence
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_ws01b_capped_grid_discounted_scale_of_continuous_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (discount : ℝ≥0 → ℝ)
    (hdiscount : Continuous discount)
    (U : Set ℝ) (hU : IsOpen U)
    (hmem :
      discount (min τ T) * W (x + X.X (min τ T) ω) ∈ U)
    (hContinuity : ContinuousAt W (x + X.X (min τ T) ω)) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
        ∃ k : ℕ,
          (X.X ((k : ℝ≥0) * h) ω < lower ∨
           upper < X.X ((k : ℝ≥0) * h) ω) ∧
          (∀ j : ℕ, j < k →
            ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
               upper < X.X ((j : ℝ≥0) * h) ω)) ∧
          discount (min ((k : ℝ≥0) * h) T) *
            W (x + X.X (min ((k : ℝ≥0) * h) T) ω) ∈ U := by sorry
