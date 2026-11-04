-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:24:47.169953+00:00
-- url     : https://prove2.me/theorems/37425aad-befd-47f8-994f-fb7c92a9d3ff
-- title:
--   Public original any-cap book and post-rightpayment V=w identity
-- statement:
--   Under the original admissible spectrally negative Levy strategy and original cap invariant, the cap-linear extension V agrees with w on the actual book reserve and its after-rightpayment reserve at every physical time, including zero and cap contact and an infinite cap. This public bridge uses only the Proved original finite-real-cap invariant and rightLimit monotonicity; it allows P3-C to replace V by w in the strict stopped terminal.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_realcap_invariant_all_times
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      V (riskProcess X x D t ω) =
        w (riskProcess X x D t ω) ∧
      V (x + X.X t ω - rightLimit D t ω) =
        w (x + X.X t ω - rightLimit D t ω) := by sorry
