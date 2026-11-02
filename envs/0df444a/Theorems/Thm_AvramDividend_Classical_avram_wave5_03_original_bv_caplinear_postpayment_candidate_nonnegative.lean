-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_bv_caplinear_postpayment_candidate_nonnegative
-- name    : AvramDividend.Classical.avram_wave5_03_original_bv_caplinear_postpayment_candidate_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:30:54.717639+00:00
-- url     : https://prove2.me/theorems/5c1ea3f2-6562-4a84-aafb-e5ee628a4d44
-- title:
--   Actual original BV-compatible cap-linear postpayment verification value is nonnegative at every time
-- statement:
--   For the actual original spectrally negative Lévy path with an admissible positive-cap dividend strategy, a C1 HJB candidate w with the indispensable w(0)≥0, zero extension below ruin, continuous boundary and derivative floor 1 has nonnegative cap-linearly extended verification value V at every genuine postpayment reserve x+X_t-D_{t+}, including the first right-payment atom, cap contact and negative overshoot. The result does not assume global nonnegativity of w nor a martingale identity. It composes the Proved original-source BV gradient terminal sign, the capped postpayment reserve upper bound, and the canonically Proved cap-linear equality on closed capped states; negative postpayment states are handled directly from the defining cap extension. This true source terminal sign is the only nontrivial boundary lemma needed to pass the integrator's complete Stieltjes finite-grid inequality to an expected reward inequality with explicit integrability.
-- source:
--   Canonical source 28b04520, 16104f4f, 85617d04. Original X, D, rightLimit and IsAdmissibleLe as in BV ef7e6c20 and corrected UBV 429e17ca (C2 implies C1).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_bv_caplinear_postpayment_candidate_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w V : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ V (x + X.X t ω - rightLimit D t ω) := by sorry
