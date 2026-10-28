-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_ennreal_expectation_rightContinuous_of_uniform_l2
-- name    : AvramDividend.Classical.chat04_killed_scale_ennreal_expectation_rightContinuous_of_uniform_l2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:51:55.737592+00:00
-- url     : https://prove2.me/theorems/b9959949-d366-46dc-bfe7-a7d557758ea9
-- title:
--   Right-continuity of ENNReal expected killed q-scale reward from uniform second moments
-- statement:
--   The expected nonnegative reward of the q-scale function killed upon negative-reserve history is right-continuous in extended-nonnegative reals for all deterministic horizons when W(0)=0. Follows from the proved uniform-L² real expectation continuity and the proved pointwise real-to-ENNReal integral bridge.
-- source:
--   Proved full-history real/ENNReal integral bridge and direct expected real right-continuity theorem, plus Mathlib ENNReal.continuous_ofReal.

import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_expectation_rightContinuous_of_uniform_l2
import Theorems.Thm_AvramDividend_Classical_chat04_history_killed_scale_real_ennreal_integral_bridge
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_scale_ennreal_expectation_rightContinuous_of_uniform_l2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (t₀ : ℝ≥0) :
    ContinuousWithinAt
      (fun t : ℝ≥0 => ∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)
      (Ici t₀) t₀ := by sorry
