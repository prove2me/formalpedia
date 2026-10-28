-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_true_killed_scale_joint_infimum_drawdown_law_ws01a
-- name    : AvramDividend.Classical.chat04_true_killed_scale_joint_infimum_drawdown_law_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:06:19.252662+00:00
-- url     : https://prove2.me/theorems/dc47bc21-59f9-4f77-a385-246323070da6
-- title:
--   True killed-scale expectation as the joint reflected-infimum and terminal drawdown law
-- statement:
--   Identify the actual finite-horizon lower-killed discounted q-scale expectation with integration over the genuine joint pushforward law of the negative running infimum L and terminal drawdown Y=X_t+L. The survival event is L≤x and the payoff becomes W(x−L+Y). This requires only the genuine process, its existing q-scale, measurability, and the proved pathwise lower-survival identity. It does not assume Wiener–Hopf independence, density, two-sided exit or martingale harmonicity. The result is the stochastic bridge to a future independent factorisation of that joint law.
-- source:
--   Canonical Proved reflected-infimum survival equivalence 3e4d270c, running infimum measurability d11a34c7, joint Lévy state measurability d55462c3, scale-function measurability 344f3813, pinned Mathlib lintegral_map.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_true_killed_scale_joint_infimum_drawdown_law_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (x q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    (∫⁻ ω : Ω,
      if ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω
      then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))
      else (0 : ℝ≥0∞) ∂P) =
    (∫⁻ z : ℝ × ℝ,
      if z.1 ≤ x
      then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (x - z.1 + z.2))
      else (0 : ℝ≥0∞)
      ∂(P.map (fun ω : Ω =>
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω},
         X.X t ω + -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})))) := by sorry
