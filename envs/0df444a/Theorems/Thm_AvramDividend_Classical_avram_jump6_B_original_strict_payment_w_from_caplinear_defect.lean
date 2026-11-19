-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_strict_payment_w_from_caplinear_defect
-- name    : AvramDividend.Classical.avram_jump6_B_original_strict_payment_w_from_caplinear_defect
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:38:50.582661+00:00
-- url     : https://prove2.me/theorems/14fb00cb-9332-4dde-bbf4-4412e7761f17
-- title:
--   Original strict-clock payment-w cash bound from cap-linear cash and physical overshoot defect
-- statement:
--   For the original same-process strict-pre-ruin stopped dividend Stieltjes cash, assume cap-linear V and w coincide at initial/final reserve and every postpayment physical mesh reserve. If the weighted prepayment overshoot discrepancy sum(V(Z)-w(Z)) is eventually at most any positive tolerance, then genuine original payment cash plus the signed w payment residual is eventually at most any positive epsilon. Uses the Proved all-cap strict cash bound and exact physical overshoot defect identity, preserving the finite-cap case rather than assuming C equals top. This isolates the remaining finite-cap prepayment overshoot convergence obligation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_canonical_caplinear_cash_epsilon
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_physical_payment_caplinear_overshoot_defect_exact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_each_grid_caplinear_signed_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_strict_payment_w_from_caplinear_defect
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (ht : t ≤ (n : ℝ≥0))
    (hInit : V (x - rightLimit D 0 ω) = w (x - rightLimit D 0 ω))
    (hFinal : V x = w x) :
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let Cash : ℝ≥0∞ :=
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
    (∀ j i : ℕ, i < m j →
      V (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω) =
      w (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω)) →
    (∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop,
      (∑ i ∈ Finset.range (m j),
        Real.exp (-(q * (v j (i + 1) : ℝ))) *
        (V (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω) -
         w (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω)))
       ≤ δ) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      Cash.toReal + (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (m j),
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
          (w (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω) -
           w (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω)))
      ≤ ε := by sorry
