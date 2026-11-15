-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign
-- name    : AvramDividend.Classical.avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:58:47.605207+00:00
-- url     : https://prove2.me/theorems/6df81ca4-c627-4d6b-9419-37701717d12f
-- title:
--   Original masked pre-ruin discounted generator HJB drift plus all time-zero-inclusive right dividend jump corrections is nonpositive on a finite physical mesh
-- statement:
--   On the same original Lévy and dividend strategy X,D, combine two genuine B219 physical cash ledger sign contributions without replacing the physical stopped reserve: (i) the discounted generator residual over strictly pre-ruin Boolean-active finite physical cells, where positive strict cap reserve and the true generator HJB inequality apply, and (ii) the discounted original right-dividend payment jump cash-minus-candidate-value correction across any finite set of genuine payment times at t=0 or strictly before ruin. Both contributions are nonpositive independently by strict physical HJB generator sign and the actual original right-payment inequality, hence their total finite source cash correction is nonpositive. This is the exact aggregate sign needed in the full stopped Itô-Meyer source after the missing Gaussian and marked martingale compensation, continuous Stieltjes dividends and true negative terminal ruin-contact contributions are accounted for. The assertion itself does not claim those remaining source identities.
-- source:
--   True original masked HJB and original right-payment discrete Stieltjes cash sign component theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (y : ι → ℝ) (active : ι → Bool)
    (hTimes : ∀ i ∈ S, s i ≤ t i)
    (hInterior : ∀ i ∈ S, active i = true →
      0 < y i ∧ ENNReal.ofReal (y i) < C)
    (ω : Ω) (R : Finset ℝ≥0)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ i ∈ S, if active i then
      Real.exp (-(q * (s i : ℝ))) *
        ((t i : ℝ) - (s i : ℝ)) *
        (X.generator w (y i) - q * w (y i))
      else 0) +
    (∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
      ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω))))) ≤ 0 := by sorry
