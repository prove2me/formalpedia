-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_piecewise_postpayment_caplinear_L1_from_discounted_Term
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_piecewise_postpayment_caplinear_L1_from_discounted_Term
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:10:33.663199+00:00
-- url     : https://prove2.me/theorems/d51653c8-94c7-4a3a-af33-f6d8b75a71c7
-- title:
--   Actual original stopped cap-linear V(W) is L1 from the discounted terminal L1 witness at bounded clock
-- statement:
--   For the original capped Lévy dividend process, exact piecewise stopped W and exact discounted terminal Term, transfer Integrable Term to Integrable (V∘W) at a bounded measurable clock. All P4-F reserve branches are covered, including time zero, cap contact, positive ruin and an infinite cap. The source cap identifies V(W) with w(W); the positive bounded exponential multiplier removes the discount via pinned Mathlib Integrable.bdd_mul. This discharges the actual postpayment value L1 premise in the Proved P4-D signed stopped branch theorem when P4-F supplies terminal integrability.
-- source:
--   Proved original caplinear book/post-rightpayment equality 37425aad-befd-47f8-994f-fb7c92a9d3ff and source P4-F Term definition; pinned Mathlib Integrable.bdd_mul and Real.exp cancellation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_original_piecewise_postpayment_caplinear_L1_from_discounted_Term
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (H : ℝ≥0)
    (hτbound : ∀ ω, τ ω ≤ H)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P) :
    Integrable (fun ω => V (W ω)) P := by sorry
