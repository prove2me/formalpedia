-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_piecewise_postpayment_stopped_V_eq_w
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_piecewise_postpayment_stopped_V_eq_w
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:07:05.26761+00:00
-- url     : https://prove2.me/theorems/b5d88c0c-62db-44e1-9b44-28963b69c0ca
-- title:
--   Original UBV stopped post-rightpayment terminal cap-linear extension agrees exactly with w
-- statement:
--   At every sample path, the literal original P4-F piecewise W is either x+X at the exact clock minus the rightLimit dividend, or the original riskProcess at the exact clock. Under the genuine admissible cap constraint, the Proved original pathwise any-cap identity 37425aad identifies the cap-linear extension V with w in both branches. This includes the initial right payment, the strictly pre-ruin horizon and the positive-ruin reserve without extra smoothness.
-- source:
--   Proved original admissible any-cap book and post-rightpayment identity 37425aad-befd-47f8-994f-fb7c92a9d3ff, applied by exact original P4-F W branch cases.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_original_piecewise_postpayment_stopped_V_eq_w
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω : Ω, V (W ω) = w (W ω) := by sorry
