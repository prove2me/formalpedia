-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_zero_or_strict_payment_residual_cash_epsilon
-- name    : AvramDividend.Classical.avram_jump6_B_original_topcap_zero_or_strict_payment_residual_cash_epsilon
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:46:45.628207+00:00
-- url     : https://prove2.me/theorems/6989672f-9a66-414d-93d8-fc963af9a462
-- title:
--   Original topcap zero-or-strict physical payment cash residual tends nonpositive
-- statement:
--   The original top-cap signed physical payment-residual cash has eventual epsilon upper bound at any stopping clock that is zero or strictly before true ruin. Strict positive clocks follow the source-exact topcap strict discounted cash theorem; at zero the grid has no Ioc payment cells, the original cash is the initial right atom, and admissibility plus the source jump-payment inequality bounds that atom and initial w reduction. No finite-activity or source substitution.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_strict_source_payment_residual_cash_epsilon
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_canonical_caplinear_cash_epsilon
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_payment_residual_signed_sum_rearrange
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_each_grid_caplinear_signed_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_topcap_zero_or_strict_payment_residual_cash_epsilon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ η (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D s η - D s η ≤
        w (riskProcess X x D s η) -
        w (riskProcess X x D s η - (rightLimit D s η - D s η)))
    (ω : Ω) (t : ℝ≥0)
    (hClock : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (ht : t ≤ (n : ℝ≥0)) :
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let Cash : ℝ≥0∞ :=
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop,
      Cash.toReal + (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (m j),
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
          (w (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω) -
            w (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω)))
      ≤ ε := by sorry
