-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stop_full_stieltjes_Hdiv_L1_ae_nonpos_from_Term_and_source_exp
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_true_stop_full_stieltjes_Hdiv_L1_ae_nonpos_from_Term_and_source_exp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:33:11.235524+00:00
-- url     : https://prove2.me/theorems/d5adbc8c-ead4-4d8e-bab5-f76e0c318bc8
-- title:
--   Original stopped full Stieltjes signed dividend residual is L1 and a.e. nonpositive from true Cash and Term
-- statement:
--   Combine the genuine original time-zero-or-strict-survival measurable branch, the original cap-linear postpayment V(W) L1 transfer from the actual discounted Term at a bounded clock, and a same-source exponential-envelope L1 for V(x+X_τ). Invoke the existing Proved source-specific full-Stieltjes signed pre-ruin branch 3211d486. The conclusion is a concrete integrable H_div≤0 a.e. for P4-F with exact original Cash paymentTimes, including singular-continuous dividend payments, the initial atom and the closed horizon. The global exponential value envelope remains an explicit independently provable growth premise.
-- source:
--   Proved source exact signed dividend branch 3211d486, new P4-D measurable branch 5c4bcbc9, new discounted Term L1 transfer d51653c8, new genuine original raw-source envelope L1 aa6fd1eb.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_preruin_branch_measurable_from_clock
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_piecewise_postpayment_caplinear_L1_from_discounted_Term
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_of_exp_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_branch_L1_ae_nonpos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_true_stop_full_stieltjes_Hdiv_L1_ae_nonpos_from_Term_and_source_exp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal))
    (hVmeas : Measurable V)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (τ : Ω → ℝ≥0) (H : ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ H)
    (hXstopped : Measurable (fun ω => X.X (τ ω) ω))
    (K : ℝ) (hK : 0 ≤ K)
    (hEnvelope : ∀ z : ℝ, ‖V z‖ ≤ K * Real.exp z)
    (W Cash Term Hdiv : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P)
    (hHdiv : ∀ ω, Hdiv ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Cash ω + (V (W ω) - V (x + X.X (τ ω) ω))
      else 0) :
    Integrable Hdiv P ∧ ∀ᵐ ω ∂P, Hdiv ω ≤ 0 := by sorry
