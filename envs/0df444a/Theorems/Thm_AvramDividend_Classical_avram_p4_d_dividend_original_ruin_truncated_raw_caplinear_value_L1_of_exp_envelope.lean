-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_of_exp_envelope
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_of_exp_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:19:17.473443+00:00
-- url     : https://prove2.me/theorems/aa6fd1eb-b12f-4254-89de-0249bdb4d53b
-- title:
--   Original stopped raw comparison value is L1 under an explicit global exponential cap-linear envelope
-- statement:
--   For the genuine original spectrally negative Lévy process, use its Proved θ=1 stopped exponential moment at τ=min(ruinTime,n) to establish L1 of the actual uncontrolled comparison value V(x+X_τ) whenever the candidate V has a stated measurable global exponential envelope. This supplies the second value L1 premise of the P4-D signed dividend remainder, while keeping the finite-cap/infinite-cap envelope as a visible independent proof obligation rather than assuming it from the HJB.
-- source:
--   Proved original ruin-truncated source exponential moment 51ec0583-746d-46ed-9584-8dd54835c9e0; pinned Mathlib Integrable.mono and real exponential multiplication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_of_exp_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (V : ℝ → ℝ) (hVmeas : Measurable V)
    (hXstopped : Measurable (fun ω => X.X (τ ω) ω))
    (K : ℝ) (hK : 0 ≤ K)
    (hEnvelope : ∀ z : ℝ, ‖V z‖ ≤ K * Real.exp z) :
    Integrable (fun ω => V (x + X.X (τ ω) ω)) P := by sorry
