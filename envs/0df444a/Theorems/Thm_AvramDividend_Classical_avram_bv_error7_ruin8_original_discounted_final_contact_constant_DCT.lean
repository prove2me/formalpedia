-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_discounted_final_contact_constant_DCT
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_original_discounted_final_contact_constant_DCT
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:02:14.315971+00:00
-- url     : https://prove2.me/theorems/af95aaba-c49f-41b7-bfc2-15bf90ca649a
-- title:
--   Actual stopped physical time discount preserves vanishing expected positive contact error under uniform domination
-- statement:
--   For the original standing Levy probability and the actual stopped physical-grid discount factor, the discounted contact error is no larger in absolute value than an undiscounted error. A.e. vanishing and uniform integrable domination of the raw error give vanishing positive expected discounted error, with measurability checked for the discounted source itself.
-- source:
--   Since q and the stopped grid time are nonnegative, the exact real discount exp(-q u_(k-1)) belongs to [0,1]. This yields norm domination and a.e. convergence of the discounted error from the raw contact error via a metric epsilon argument. The Proved original probability constant-DCT then supplies integrability and expectation convergence; no BV dividend budget enters.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_probability_constant_dom_positive_DCT
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_original_discounted_final_contact_constant_DCT
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (K : ℝ) (hK : 0 ≤ K)
    (Raw Disc : ℕ → Ω → ℝ)
    (hRawAE : ∀ᵐ ω ∂P, Tendsto (fun m => Raw m ω) atTop (nhds (0 : ℝ)))
    (hRawDom : ∀ m, ∀ᵐ ω ∂P, ‖Raw m ω‖ ≤ K)
    (hDiscSource : ∀ m ω, Disc m ω =
      Real.exp (-(q * (u m (k m ω - 1) : ℝ))) * Raw m ω)
    (hDiscMeas : ∀ m, AEStronglyMeasurable (Disc m) P) :
    (∀ m, Integrable (fun ω => max (Disc m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Disc m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
