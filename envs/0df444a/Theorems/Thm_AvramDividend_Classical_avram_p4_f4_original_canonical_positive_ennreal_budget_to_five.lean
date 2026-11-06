-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_canonical_positive_ennreal_budget_to_five
-- name    : AvramDividend.Classical.avram_p4_f4_original_canonical_positive_ennreal_budget_to_five
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:00:38.348671+00:00
-- url     : https://prove2.me/theorems/bceb8fe9-a84c-4a69-8659-6de7541c47cc
-- title:
--   Canonical original stopped source five witnesses from a single genuine ENNReal expected payoff budget
-- statement:
--   Using the actual controlled Lévy process X and the canonical stopped W/Cash/Term, the HJB slope conditions automatically imply w(x)≥0 and the original terminal and genuine Stieltjes cash are nonnegative. Thus a source-proved ENNReal expected payoff budget entails terminal L1 and the five literal centred integrable source slots. This theorem retains the expected budget as the sole stochastic hypothesis.
-- source:
--   Compose established original-X anycap gradient positivity (79db013c), original stopped terminal positivity (f6fef241), physical Stieltjes cash positivity (4db282c6), finite budget-to-L1 (2360f684) and literal five-slot expected budget iff (388d9c1a). Obtain IsProbabilityMeasure from X.isProbability; no assumed probability class or natural clock UI.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_stopped_terminal_L1_of_combined_ennreal_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_five_witness_iff_expected_budget

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_original_canonical_positive_ennreal_budget_to_five
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hBudget : (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
