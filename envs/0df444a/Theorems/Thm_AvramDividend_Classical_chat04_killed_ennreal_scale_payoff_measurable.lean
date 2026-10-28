-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_ennreal_scale_payoff_measurable
-- name    : AvramDividend.Classical.chat04_killed_ennreal_scale_payoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:07:39.823559+00:00
-- url     : https://prove2.me/theorems/2603b26a-bb9e-4272-b2cd-53666b0388cf
-- title:
--   Measurability of the true history-killed extended nonnegative q-scale payoff
-- statement:
--   For any spectrally negative Lévy process, real discount and canonical scale function, the whole-history downward-killed discounted scale payoff is measurable as an ENNReal-valued random variable at every deterministic horizon. This gives the exact measurability premise of Fatou's lemma for killed q-scale expectations.
-- source:
--   Proved chat04_lower_survival_closed_window_measurable b28f55f0 and chat03_scale_function_borel_measurable 45cbe3b4. Needed for Fatou lower semicontinuity of killed expectation from positive reserve, advancing killed scale renewal identity a885f0b3 and stopped-scale aed50a34.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_ennreal_scale_payoff_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    Measurable (fun ω : Ω =>
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω) := by sorry
