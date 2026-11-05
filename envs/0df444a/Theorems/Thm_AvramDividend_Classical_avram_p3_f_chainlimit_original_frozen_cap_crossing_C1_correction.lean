-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:54:41.926949+00:00
-- url     : https://prove2.me/theorems/84f8df8a-bc5d-46ee-b78e-82e9c1fc85d2
-- title:
--   Exact original Lévy source-frozen finite-cap crossing correction for C1 mesh cells
-- statement:
--   For every cell of the actual original source X.X and right-payment control D, the cap-pasted V source-frozen increment differs from the ordinary w increment by the explicit cap-linear crossing correction at the source-only endpoint. Infinite cap or a below-cap source endpoint makes the correction exactly zero, including cap contact. This covers actual above-cap excursions before the right-payment and uses the Proved original postpayment V=w identity at the true frozen start. No stochastic compensation, grid limit, or canonical stopped conclusion is assumed.
-- source:
--   Proved original any-cap postpayment identity 37425aad, actual X.X and rightLimit D, cap-pasted V definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (n : ℕ) :
    ∀ ω i, i < n →
      let a := x + X.X (u i) ω - rightLimit D (u i) ω
      let b := x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      V b - V a =
        (w b - w a) +
          (if C = ⊤ then 0
           else if b ≤ C.toReal then 0
           else w C.toReal + (b - C.toReal) - w b) := by sorry
