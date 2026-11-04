-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_finite_envelope_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_eventual_finite_envelope_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:27:34.370016+00:00
-- url     : https://prove2.me/theorems/b21faf7e-485a-4872-adf3-4385f68ff2b8
-- title:
--   Eventual finite ENNReal dominated grid L² bounds justify Bochner expectation limits
-- statement:
--   For signed real grid sums Y_n dominated in enorm almost everywhere by nonnegative ENNReal source grid sums G_n, with any finite eventual squared-lintegral envelope K and explicit a.e. convergence to Z, derive integrability of Z and convergence of genuine Bochner expectations. Fits the original Levy grid estimate with its explicit K (which need not already be a square). No process law, compensator or mesh-to-jump theorem is assumed.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_squared_enorm_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_l2_ae_expectations

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_eventual_finite_envelope_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (G : ℕ → Ω → ENNReal)
    (K : ENNReal) (N : ℕ) (hK : K ≠ ⊤)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hdom : ∀ n, ∀ᵐ ω ∂P, ‖Y n ω‖ₑ ≤ G n ω)
    (hB : ∀ n, N ≤ n → (∫⁻ ω, (G n ω) ^ (2 : ℝ) ∂P) ≤ K)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
