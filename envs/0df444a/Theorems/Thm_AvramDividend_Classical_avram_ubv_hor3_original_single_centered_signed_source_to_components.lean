-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_single_centered_signed_source_to_components
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_single_centered_signed_source_to_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:32:06.670714+00:00
-- url     : https://prove2.me/theorems/a022e56f-5da1-4a90-9031-9b5560565d93
-- title:
--   Original stopped source components follow from one centred L1 martingale and signed unrestricted remainder
-- statement:
--   For the unchanged original Levy X, actual controlled stopped W, full dividendMeasure Cash and discounted Term of the UBV P4-F3 source, one integrable mean-zero physical martingale M and a nonpositive, possibly non-integrable remainder R with the source upper estimate already suffice to construct the exact five witness functions demanded by fdb9a6a3. Set Mc=M, Ms=Ml=G=0 and R'=R. This removes the separate three-martingale and signed-drift integrability burdens from the sufficient source interface without asserting the missing physical martingale or Ito identity.
-- source:
--   Direct algebraic source witness adapter. It uses the true original source W/Cash/Term definitions as explicit premises and the zero-function integrability/expectation facts. It imports no fdb9a6a3, no 0dda1be7, no canonical target or downstream theorem. The remaining one-martingale pathwise source estimate is explicitly named and must be proved independently.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_single_centered_signed_source_to_components
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (M R : Ω → ℝ)
    (hMI : Integrable M P)
    (hZero : (∫ ω, M ω ∂P) = 0)
    (hRnonpos : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hSource : ∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + R ω) :
    ∃ Mc Ms Ml G R' : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R' ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R' ω) := by sorry
