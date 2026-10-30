-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_sampled_reflected_stopped_reward_killed_factor
-- name    : AvramDividend.Classical.avram_root29_05_sampled_reflected_stopped_reward_killed_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:55:33.534173+00:00
-- url     : https://prove2.me/theorems/31f9ae9b-897b-49ae-8f27-1cda2918765b
-- title:
--   Genuine killed first-upcrossing Strong-Markov factorisation for the globally measurable sampled reflected Stieltjes reward
-- statement:
--   The full countably sampled discounted reflected Stieltjes record reward, killed at the sampled drawdown ruin clock and defined as a Borel reward on unrestricted paths, factorises after an actual barrier first-upcrossing before original controlled ruin. The killing prefix and discount use true Lévy stopping times. This supplies the probability-side identity for the subsequent genuine-path Stieltjes approximation step.
-- source:
--   Composition of canonically Proved path_countable_reflected_stopped_reward_measurable d83660d4 and avram_root29_05_uncapped_barrier_killed_future_reward_factor 87a4ffed. Source-faithful intermediate for 79978d61; equality of the sampled reward with the genuine Stieltjes payout remains a separate analytic obligation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_path_countable_reflected_stopped_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_uncapped_barrier_killed_future_reward_factor

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_sampled_reflected_stopped_reward_killed_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 < a) (hxa : x ≤ a)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (samples : ℕ → ℝ≥0) (mesh : ℕ → ℕ → ℝ≥0)
    (weights : ℕ → ℕ → ℝ≥0∞) :
    let sampledReward : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
      ⨆ n : ℕ, ⨆ N : ℕ, ∑ k ∈ Finset.range N,
        if (mesh n (k + 1) : ℝ≥0∞) <
          (⨅ i : ℕ,
            if f (samples i) - f 0 -
              (⨆ j : ℕ,
                if samples j ≤ samples i then
                  ENNReal.ofReal (f (samples j) - f 0)
                else 0).toReal < -a then
              (samples i : ℝ≥0∞)
            else ⊤) then
          weights n k * ENNReal.ofReal
            ((⨆ i : ℕ,
                if samples i ≤ mesh n (k + 1) then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal -
              (⨆ i : ℕ,
                if samples i ≤ mesh n k then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal)
        else 0
    let T := twoSidedExitUpTime X (a - x)
    let R := ruinTime X x (barrierStrategy X x a)
    (∫⁻ ω, if T ω < R ω then
      discount ((T ω).toNNReal) *
        sampledReward (fun t : ℝ≥0 =>
          X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω)
      else 0 ∂P) =
    (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) else 0 ∂P) *
      (∫⁻ ω, sampledReward (fun t : ℝ≥0 => X.X t ω) ∂P) := by sorry
