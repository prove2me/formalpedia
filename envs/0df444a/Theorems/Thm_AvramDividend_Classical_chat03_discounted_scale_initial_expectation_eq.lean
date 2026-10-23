-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_initial_expectation_eq
-- name    : AvramDividend.Classical.chat03_discounted_scale_initial_expectation_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T08:08:31.777113+00:00
-- url     : https://prove2.me/theorems/f579a62f-3d35-464c-bdeb-8b09a08c5958
-- title:
--   Discounted Lévy scale payoff has the correct initial expectation
-- statement:
--   A spectrally negative Lévy process starts from zero and carries a probability measure. Therefore for any initial capital x, scale function candidate W, discount q, and sampling clock starting at zero, the initial expected discounted reward equals W(x). This removes a redundant initial-integral hypothesis from sampled martingale verification.
-- source:
--   Use the process's pathwise X_zero property, zero clock, exp(0)=1, and the probability-measure normalisation X.isProbability.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_discounted_scale_initial_expectation_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ)
    (clock : ℕ → ℝ≥0) (hclock0 : clock 0 = 0) :
    (∫ ω, Real.exp (-(q * (clock 0 : ℝ))) *
      W (x + X.X (clock 0) ω) ∂P) = W x := by
  sorry
