-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_source_witness_components_to_stopped_cash
-- name    : AvramDividend.Classical.avram_limit1_ubv_source_witness_components_to_stopped_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:52:04.312546+00:00
-- url     : https://prove2.me/theorems/6daec776-f283-4cc5-856c-7a031322e6f8
-- title:
--   Original UBV three-martingale and sign-controlled source components imply actual bounded stopped dividend cash
-- statement:
--   The exact original P4-F public source components include real Cash equal to the .toReal of the true closed-Iic stopped dividendMeasure integral, a piecewise actual W reserve, discounted Term, three integrable zero-mean martingales, nonpositive generator and residual drift components, and the original pathwise stopped Ito-Meyer budget. Given these source witnesses (explicit existential hypothesis, not assumed proven from an Open target), the original exact min(ruinTime,n) NNReal clock identity (whose finite bound follows from the Proved P4-D clock lemma af8ae00a), and the actual UBV smoothness/gradient/cap hypotheses, Proved f6fef241 proves the exact all-branch Term is nonnegative. Add the three centred martingales and apply the previously Proved avram_limit1 bounded stopped residual to double ENNReal cash helper. No theorem asserts existence of original stochastic source components, no hypothesis is silently added, and the right-horizon and zero atoms remain.

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

theorem AvramDividend.Classical.avram_limit1_ubv_source_witness_components_to_stopped_cash
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
    (hSource : ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω)) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by sorry
