-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_payoff_nonnegative
-- name    : AvramDividend.Classical.chat04_killed_scale_payoff_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:54:16.216982+00:00
-- url     : https://prove2.me/theorems/e76813d3-1150-4c38-b38b-04c807851877
-- title:
--   Every history-killed q-scale payoff is nonnegative at all times and reserves
-- statement:
--   A canonical q-scale function is everywhere nonnegative, exponential discounts are strictly positive, and the history survival indicator preserves nonnegativity. Hence, for all real starting reserves and every finite observation time, the genuinely killed q-scale payoff is nonnegative pathwise. This lemma does not assume Standing or a martingale and supplies the nonnegative terminal reward needed for Fatou and optional stopping.

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat04_killed_scale_payoff_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) :
    ∀ (t : ℝ≥0) (ω : Ω),
      0 ≤ ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}.indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) := by sorry
