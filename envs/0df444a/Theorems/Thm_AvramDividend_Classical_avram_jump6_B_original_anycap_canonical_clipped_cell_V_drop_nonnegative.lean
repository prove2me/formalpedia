-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_canonical_clipped_cell_V_drop_nonnegative
-- name    : AvramDividend.Classical.avram_jump6_B_original_anycap_canonical_clipped_cell_V_drop_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:16:38.399963+00:00
-- url     : https://prove2.me/theorems/513add51-428f-4bc8-aa81-c38a5c4b8f1a
-- title:
--   True original finite/infinite cap canonical stopped physical-grid V potential drops are nonnegative
-- statement:
--   For the original spectrally negative Levy X, an admissible strategy under any positive finite or infinite cap, and a strictly pre-ruin true stopped clock, the cap-linear extended HJB potential V has nonnegative prepayment minus postpayment potential drop in every actual clipped canonical physical mesh cell. Follows from the original rightLimit D monotonicity, genuine reserve after rightpayment positivity and the publicly proved all-cap secant. Supplies the sign needed for the original all-cap discounted Stieltjes sum and limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_previsible_caplinear_payment_drop_nonnegative
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_anycap_canonical_clipped_cell_V_drop_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω) (j i : ℕ) :
    let v : ℕ → ℝ≥0 := fun k =>
      min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    0 ≤ V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
      V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) := by sorry
