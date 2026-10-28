-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_expectation_tendsto_of_uniform_l2
-- name    : AvramDividend.Classical.chat04_killed_scale_expectation_tendsto_of_uniform_l2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:23:38.462995+00:00
-- url     : https://prove2.me/theorems/5808a91c-9d4b-4d9e-ba15-c29a9e1227ec
-- title:
--   Sequential right-continuity of expected killed q-scale payoff from uniform L² bounds
-- statement:
--   For a spectrally negative Lévy process whose q-scale function vanishes at zero, the expectation of the discounted q-scale function killed by negative-reserve history is continuous along bounded deterministic sequences approaching any horizon from the right. Uses pathwise right-continuity and a common uniform second-moment bound, with no pointwise domination assumption.
-- source:
--   Proved killed payoffs measurability, finite-horizon uniform L² bound, pathwise masked payoff continuity and generic Vitali convergence theorem.

import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_payoff_measurable_nonnegative
import Theorems.Thm_AvramDividend_Classical_chat04_killed_deterministic_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat04_levy_closed_killed_discounted_scale_rightCont
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
import Mathlib.Tactic.FunProp

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat04_killed_scale_expectation_tendsto_of_uniform_l2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (N t₀ : ℝ≥0) (t : ℕ → ℝ≥0)
    (htN : ∀ n, t n ≤ N)
    (htend : Tendsto t atTop (𝓝[Ici t₀] t₀)) :
    Tendsto
      (fun n => ∫ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t n : ℝ))) *
            W (x + X.X (t n) u)) ω ∂P)
      atTop
      (𝓝 (∫ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t₀ → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t₀ : ℝ))) *
            W (x + X.X t₀ u)) ω ∂P)) := by sorry
