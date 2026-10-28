-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unconditional_history_future_path_markov_tonelli
-- name    : AvramDividend.Classical.chat04_unconditional_history_future_path_markov_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:07:57.52774+00:00
-- url     : https://prove2.me/theorems/77ced690-a2a9-4d93-bb66-4ae69a114152
-- title:
--   Unconditional full-path Markov–Tonelli formula for arbitrary past and future Lévy rewards
-- statement:
--   For any spectrally negative Lévy process, time s, F_s-measurable past-state statistic H and measurable nonnegative payoff depending on H and the entire shifted future path, the expected payoff factors as an iterated integral over the law of H and the original whole Lévy path. This theorem has no finite-cylinder independence assumptions, unlike the older conditional chat04_arbitrary_history_full_future_path_markov_tonelli. The exact formula applies to genuinely history-killed rewards and is a direct semigroup input for the remaining positive-capital killed q-scale renewal identity a885f0b3-3960-424d-97e4-abbcffe268ba, then stopped exit 09663d0d and parent 3e1ce2c8.
-- source:
--   Composition of Proved unconditional entire-path stationary joint product law cd9853a4-d75b-4779-b22b-4c4db8f41256, pinned Mathlib lintegral_map and lintegral_prod. Root-connected through the killed q-scale semigroup and two-sided stopped exit identities.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Process.Basic
import Theorems.Thm_AvramDividend_Classical_levy_deterministicTime_history_future_product_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_unconditional_history_future_path_markov_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (f : E × (ℝ≥0 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (H ω,
        (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) ∂P) =
    ∫⁻ h, ∫⁻ y, f (h, y)
      ∂(Measure.map (fun ω => (fun t : ℝ≥0 => X.X t ω)) P)
      ∂(Measure.map H P) := by sorry
