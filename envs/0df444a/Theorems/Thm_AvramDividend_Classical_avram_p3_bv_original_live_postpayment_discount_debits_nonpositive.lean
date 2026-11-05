-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_live_postpayment_discount_debits_nonpositive
-- name    : AvramDividend.Classical.avram_p3_bv_original_live_postpayment_discount_debits_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:23:08.704748+00:00
-- url     : https://prove2.me/theorems/bd47bbd5-28d4-42e7-95e7-eeef1eee94be
-- title:
--   Original zero-or-strict-pre-ruin physical postpayment discount correction is nonpositive at every cap
-- statement:
--   For an actual original admissible dividend strategy and nonnegative discount rate, the finite sum of all physical mesh negative exponential discount decrements multiplied by the real cap-linear verification candidate at the true post-rightpayment reserve is nonpositive whenever all cell endpoints are time zero or strictly pre-ruin. No additional positive-value assumptions or finite cap restrictions are imposed.
-- source:
--   Source-exact original reserve nonnegativity d6323bfa and all-cap C1 verification nonnegativity 6f389e8f, with exponential monotonicity. Removes signed discount debris from original full Stieltjes source grid for the Open db6a3111 pathwise stopped certificate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Every physical postpayment source discount decrement is nonpositive
   while its actual original clock is zero or strictly before ruin. -/

theorem AvramDividend.Classical.avram_p3_bv_original_live_postpayment_discount_debits_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (hq : 0 ≤ q)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) *
      (if C = ⊤ then
        w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
       else if x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω ≤ C.toReal
       then w (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
       else w C.toReal +
         ((x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) - C.toReal))) ≤ 0 := by sorry
