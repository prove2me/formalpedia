-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_frozen_source_cap_V_eq_w
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_frozen_source_cap_V_eq_w
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:51:45.951958+00:00
-- url     : https://prove2.me/theorems/85a79985-138c-49db-8c47-49c8fb354adb
-- title:
--   Original source-frozen V equals w across any below-cap physical source cell, including cap contact
-- statement:
--   For the true original Lévy source and admissible right-payment control, the cap-pasted verification function V agrees with w at each actual postpayment grid state. If the source-only endpoint of a cell lies on or below the finite cap, V also agrees with w at the physical source-frozen endpoint, yielding the exact frozen V-to-w increment identity required by the original strict-open C1 mesh budget. The cap inequality includes contact and is explicit for the localisation owner to establish. Infinite cap is unconditional.
-- source:
--   Proved public original any-cap book/postpayment V=w theorem 37425aad plus exact cap-pasted V definition and the true X.X source-only frozen endpoint.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_frozen_source_cap_V_eq_w
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
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hFrozenCap : ∀ ω i, i < n → C ≠ ⊤ →
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω ≤ C.toReal) :
    ∀ ω i, i < n →
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        V (x + X.X (u i) ω - rightLimit D (u i) ω) =
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω) := by sorry
