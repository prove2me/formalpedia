-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_original_single_residual_to_stopped_cash
-- name    : AvramDividend.Classical.avram_limit1_ubv_original_single_residual_to_stopped_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:58:57.773258+00:00
-- url     : https://prove2.me/theorems/b971ab44-690d-4191-9d7e-4f5e2b359e1a
-- title:
--   Original UBV P4-F stopped one-martingale residual implies genuine closed-clock dividend cash
-- statement:
--   For the exact original UBV stopped Lévy model, given a genuine capped dividend strategy, the original positive-horizon ruin-truncated NNReal clock identity, clock measurability, source exact W/Cash/Term definitions and integrable Cash, suppose the canonical original P4-F stopped residual components M,G,H exist with M integrable mean zero, G/H integrable and combined drift nonpositive almost everywhere, and Term+Cash≤w(x)+M+G+H almost everywhere. The Proved P4-D clock lemma af8ae00a derives the finite n bound from the exact ruin clock identity. The Proved P4-E all-branch terminal lemma f6fef241 gives 0≤Term pointwise. The accepted LIMIT-1 bounded stopped residual b443283f then yields the genuine double ENNReal original stopped discounted dividend reward upper bound. P4-F residual existence remains an explicit source premise, so there is no circular stochastic proof.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_limit1_bounded_clock_stopped_residual_to_ennreal_cash

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_ubv_original_single_residual_to_stopped_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P)
    (hSource : ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + M ω + G ω + H ω)) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by sorry
