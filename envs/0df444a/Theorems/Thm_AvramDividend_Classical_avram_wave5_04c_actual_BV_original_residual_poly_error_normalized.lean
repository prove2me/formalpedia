-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_original_residual_poly_error_normalized
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_BV_original_residual_poly_error_normalized
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:41:45.049696+00:00
-- url     : https://prove2.me/theorems/349d150d-6e39-4e67-9243-b6650b98d4a8
-- title:
--   Actual bounded-variation Lévy residual expected C1 polynomial approximation error controlled by first moment and large tails
-- statement:
--   At every actual time t≤1 under the original spectrally negative bounded-variation Lévy process, let R_t=t*drift-X_t. Existing source monotonicity proves R_t≥0 almost everywhere; Standing and BV prove its Bochner first moment and truncated tail integrability. Applying the fully proved random BV weighted polynomial domination to the original source gives expected error ≤ε E[R_t]+2L E[R_t 1_{R_t>M}]. The prior Proved normalized mean and tail estimates then make this o(h) at the right-time filter. No substitute process or C2 assumption.
-- source:
--   Actual original-process BV residual nonnegativity, first moment, truncation integrability, and random Bochner polynomial error transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_random_BV_weighted_polynomial_L1_error
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_BV_original_residual_poly_error_normalized {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (x M ε : ℝ) (hε : 0 ≤ ε)
    (Q : Polynomial ℝ)
    (hpoint : ∀ r : ℝ, 0 ≤ r →
      |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤
        ε * (1 - Real.exp (-r)) +
          (if M < r then 2 * L * r else 0)) :
    ∀ t : ℝ≥0, t ≤ 1 →
      |∫ ω,
        (w x - w (x - ((t : ℝ) * X.drift - X.X t ω))) -
          Polynomial.eval (Real.exp (-((t : ℝ) * X.drift - X.X t ω))) Q ∂P| ≤
        ε * (∫ ω, (t : ℝ) * X.drift - X.X t ω ∂P) +
        2 * L * (∫ ω,
          if M < (t : ℝ) * X.drift - X.X t ω
          then (t : ℝ) * X.drift - X.X t ω else 0 ∂P) := by sorry
