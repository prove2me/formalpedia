-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_clipped_grid_postpaid_caplinear_agrees_w
-- name    : AvramDividend.Classical.avram_jump6_B_original_clipped_grid_postpaid_caplinear_agrees_w
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T00:59:44.721391+00:00
-- url     : https://prove2.me/theorems/e0124590-083d-4e0f-85b0-e6e6468b4148
-- title:
--   Original capped dividend physical clipped-grid postpayment V equals w
-- statement:
--   For the same original spectrally negative Levy process and admissible capped dividend strategy, the cap-linear continuation V equals w at every physical postpayment reserve on the canonical clipped grid. This holds for finite and infinite caps and follows from the already Proved pathwise all-time book/postpayment agreement. Useful for eliminating a separate postpayment-agreement premise from the finite-cap source cash estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_allcap_book_postpayment_V_eq_w
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_clipped_grid_postpaid_caplinear_agrees_w
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
    (ω : Ω) (t : ℝ≥0) (n : ℕ) :
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    ∀ j i : ℕ, i < m j →
      V (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω) =
      w (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω) := by sorry
