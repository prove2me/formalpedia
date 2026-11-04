-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_branch_L1_ae_nonpos
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_stopped_branch_L1_ae_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:59:13.648889+00:00
-- url     : https://prove2.me/theorems/3211d486-ce5f-4a54-a6ed-60d54edcca5f
-- title:
--   Original stopped full-Stieltjes pre-ruin dividend branch is L1 and almost-everywhere nonpositive
-- statement:
--   Define the actual dividend signed remainder on the measurable event τ=0 or τ<ruin from canonical Cash plus the cap-linear postpayment W minus the same-source uncontrolled terminal comparison. Zero it on the positive ruin branch, which belongs to the separate crossing calculation. Under actual cash, postpayment and source terminal L1 hypotheses, the branch is integrable by the exact pinned Mathlib measurable-set indicator lemma. The full original closed Stieltjes inequality yields a pathwise nonpositive sign on the branch, hence almost everywhere. The explicit L1 premises are genuine outstanding source moment obligations for P4-F, not claims that Cash alone controls the signed residual.
-- source:
--   Actual original-source b7f6754b-bb40-4d86-bd48-aae4411986f7 full measure sign and bfe4a214-2dc7-40dc-b43d-19316d917a2e stopped domain; pinned Mathlib MeasureTheory.Integrable.indicator verified at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_stopped_branch_L1_ae_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Cash Hdiv : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hPreMeas : MeasurableSet {ω : Ω |
      τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω})
    (hCashI : Integrable Cash P)
    (hVWI : Integrable (fun ω => V (W ω)) P)
    (hVSI : Integrable (fun ω => V (x + X.X (τ ω) ω)) P)
    (hHdiv : ∀ ω, Hdiv ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Cash ω + (V (W ω) - V (x + X.X (τ ω) ω))
      else 0) :
    Integrable Hdiv P ∧ ∀ᵐ ω ∂P, Hdiv ω ≤ 0 := by sorry
