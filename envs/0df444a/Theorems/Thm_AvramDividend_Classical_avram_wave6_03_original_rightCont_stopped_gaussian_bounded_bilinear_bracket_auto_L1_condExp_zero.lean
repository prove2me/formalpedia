-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_bracket_auto_L1_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_bracket_auto_L1_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:55:45.211861+00:00
-- url     : https://prove2.me/theorems/67db9271-9459-4718-aae2-8aaeda7380ec
-- title:
--   Bounded predictable source Gaussian bilinear compensated bracket with automatic stochastic-cell L1
-- statement:
--   On the original zero-jump Levy path with its right-continuous stopping-time history, bounded predictable coefficient pairs G,H automatically give an integrable bilinear source Gaussian cell by the established L2 isometry. Assuming only that the predictable product GH is integrable, its compensator h sigma squared GH makes the bracket increment have conditional stopped-history mean zero. This removes the additional stochastic-product integrability hypothesis from the general compensated bilinear bracket theorem. Arbitrary sigma including zero is allowed; no detached Brownian process or general-nu residual is claimed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bilinear_compensated_bracket_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_bracket_auto_L1_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGglobal : Measurable G) (hHglobal : Measurable H)
    (BG BH : ℝ) (hBG : 0 ≤ BG) (hBH : 0 ≤ BH)
    (hGbound : ∀ ω, |G ω| ≤ BG)
    (hHbound : ∀ ω, |H ω| ≤ BH)
    (hGHInt : Integrable (fun ω => G ω * H ω) P) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    P[(fun ω => (G ω * Y ω) * (H ω * Y ω) -
      ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  sorry
