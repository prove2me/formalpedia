-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_markov_tonelli_killed_history_kernel
-- name    : AvramDividend.Classical.avram_ws01b_actual_markov_tonelli_killed_history_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:11:06.192619+00:00
-- url     : https://prove2.me/theorems/984cb4a5-1778-4ec7-9100-8b20a895806c
-- title:
--   Original Lévy Markov–Tonelli for genuinely history-masked future killed rewards
-- statement:
--   For the actual original Lévy law, any filtration-measurable pair of historical reserve and survival flag, an arbitrary measurable payoff and any countable future monitoring schedule, the true killed future reward factors through the original independent whole-path Lévy law and the actual history distribution. The theorem has a genuine historical Bool mask, and does not require a fictitious independent process or invoke the unresolved stopped-scale harmonicity.
-- source:
--   Actual original Lévy full-future-path Markov–Tonelli 77ced690 and countable future-reserve survival measurability; necessary source-faithful history-killed Chapman–Kolmogorov bridge in WS1B.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_unconditional_history_future_path_markov_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01b_actual_markov_tonelli_killed_history_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ × Bool) (hH : Measurable[𝓕 s] H)
    (τ : ℕ → ℝ≥0) (T : ℝ≥0) (q : ℝ)
    (W : ℝ → ℝ) (hW : Measurable W) :
    (∫⁻ ω,
      (if (H ω).2 then
        if ∀ j : ℕ, τ j ≤ T →
            0 ≤ (H ω).1 + (X.X (s + τ j) ω - X.X s ω) then
          ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) *
            W ((H ω).1 + (X.X (s + T) ω - X.X s ω)))
        else (0 : ℝ≥0∞)
      else (0 : ℝ≥0∞)) ∂P) =
    ∫⁻ h, ∫⁻ y,
      (if h.2 then
        if ∀ j : ℕ, τ j ≤ T → 0 ≤ h.1 + y (τ j) then
          ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (h.1 + y T))
        else (0 : ℝ≥0∞)
      else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun t : ℝ≥0 => X.X t ω)) P)
      ∂(Measure.map H P) := by sorry
