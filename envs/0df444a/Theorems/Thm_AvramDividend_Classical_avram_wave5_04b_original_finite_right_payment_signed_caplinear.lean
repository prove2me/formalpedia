-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_finite_right_payment_signed_caplinear
-- name    : AvramDividend.Classical.avram_wave5_04b_original_finite_right_payment_signed_caplinear
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:42:14.913953+00:00
-- url     : https://prove2.me/theorems/c53468c0-8712-4eb3-9833-e9ac4ccf6d8a
-- title:
--   Finite original-source chronological right-payment signed corrections are nonpositive at all capped boundaries
-- statement:
--   For the original adapted spectrally negative Levy process and any finite collection of genuine pre-ruin right-payment times, including t=0, the signed discounted correction consisting of each actual dividend right atom plus the corresponding cap-linear potential change is nonpositive. Source X_t is evaluated before the right dividend jump; the post-payment reserve is obtained by subtracting the exact rightLimit D_t - D_t. Admissibility establishes post-payment solvency, monotonicity establishes nonnegative payments, and the full-cap secant handles reserve zero/cap contacts and pre-payment reserve above cap. This is the atomic component of the source-specific Stieltjes correction; atomless singular-continuous payments still require the separate nonderivative measure argument.
-- source:
--   Proved full-cap cap-linear continuation 420ddace-18e0-48de-aecc-c7ccbc6c7c52; Proved dividendStrategy_le_rightLimit 953f0e91-72ae-4c01-a7d6-8c4d19980128; original IsAdmissibleLe solvency and exact chronological riskProcess. BV verification target ef7e6c20-a118-46f0-ac94-5b02204bba49.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_finite_right_payment_signed_caplinear
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (hV : ∀ y : ℝ, V y = if y ≤ c then w y else w c + (y - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (t : ℕ → ℝ≥0) (n : ℕ)
    (hPre : ∀ k : ℕ, k < n →
      t k = 0 ∨ (t k : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ k ∈ Finset.range n,
      Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          V (riskProcess X x D (t k) ω -
            (rightLimit D (t k) ω - D (t k) ω)) -
          V (riskProcess X x D (t k) ω))) ≤ 0 := by sorry
