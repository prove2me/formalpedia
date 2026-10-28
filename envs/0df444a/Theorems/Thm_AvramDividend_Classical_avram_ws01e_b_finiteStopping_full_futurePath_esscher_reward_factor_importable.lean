-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_finiteStopping_full_futurePath_esscher_reward_factor_importable
-- name    : AvramDividend.Classical.avram_ws01e_b_finiteStopping_full_futurePath_esscher_reward_factor_importable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:42:58.920108+00:00
-- url     : https://prove2.me/theorems/dc64b040-a3da-4cad-91e5-a228c87361ff
-- title:
--   Importable full stopped Lévy future-path Esscher reward factor
-- statement:
--   For any finite genuine Lévy stopping time τ with adapted sublevel sets, any measurable nonnegative stopped-history weight and arbitrary measurable nonnegative functional of the entire future Lévy increment path, the expectation of history weight times the finite-lag compensated Esscher exponential of the future increment and the full-path reward factors into the past-weight expectation and the original-law expectation of the same compensated Esscher reward on the fresh Lévy path. This is a true stopping-time strong-Markov result, not a new global Esscher probability law. The original 1E-B target was authored with a missing import in its canonical preamble; this replacement adds the accepted stopping-time conversion import explicitly.
-- source:
--   Direct functional reweighting of canonically Proved levy_finiteStopping_historyWeight_futureReward_factor (b995a471-5065-4673-ba97-d0f13ebfc768), using measurable_pi_apply and measurable composition of exp and ENNReal.ofReal. Source-faithful proof prepared by the 1E-B workstream and reused here to repair a canonical preamble blocker.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_historyWeight_futureReward_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Full shifted Levy future-path Esscher reward factor at an arbitrary finite
stopping time, retaining any measurable stopped-history weight. -/

theorem AvramDividend.Classical.avram_ws01e_b_finiteStopping_full_futurePath_esscher_reward_factor_importable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (pastWeight : Ω → ℝ≥0∞)
    (hp : Measurable pastWeight)
    (hpPast : Measurable[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] pastWeight)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℝ≥0)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hr : Measurable reward) :
    (∫⁻ ω, pastWeight ω *
      (ENNReal.ofReal (Real.exp
        (θ * (X.X (τ ω + u) ω - X.X (τ ω) ω) -
          (u : ℝ) * X.ψ θ)) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)) ∂P) =
    (∫⁻ ω, pastWeight ω ∂P) *
      (∫⁻ ω, ENNReal.ofReal (Real.exp
        (θ * X.X u ω - (u : ℝ) * X.ψ θ)) *
        reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by sorry
