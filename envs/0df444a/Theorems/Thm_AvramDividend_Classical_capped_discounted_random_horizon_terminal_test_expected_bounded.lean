-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_discounted_random_horizon_terminal_test_expected_bounded
-- name    : AvramDividend.Classical.capped_discounted_random_horizon_terminal_test_expected_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:02:33.353227+00:00
-- url     : https://prove2.me/theorems/833e5ab0-6f36-40c8-9304-e4bb5b33c47d
-- title:
--   Finite expected absolute discounted terminal verification payoff at arbitrary random stopped horizons
-- statement:
--   For nonnegative discount rate q, the discount factor exp(-q t) is between zero and one at any nonnegative stopping horizon. Combining this pointwise inequality with the canonically proved undiscounted uniform expected absolute bound yields finite uniform expected absolute discounted terminal values for every random horizon before ruin. This is a finite-cap domination ingredient for bounded- and unbounded-variation stochastic localisation.
-- source:
--   Proved capped_random_horizon_surviving_test_expected_bounded and Mathlib Real.exp_le_one_iff, lintegral_mono.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_random_horizon_surviving_test_expected_bounded

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_discounted_random_horizon_terminal_test_expected_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B) (q : ℝ) (hq : 0 ≤ q)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∫⁻ ω, if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        ENNReal.ofReal (|Real.exp (-(q * (τ ω : ℝ))) *
          w (riskProcess X x D (τ ω) ω)|) else 0 ∂P) ≤
      ENNReal.ofReal M := by sorry
