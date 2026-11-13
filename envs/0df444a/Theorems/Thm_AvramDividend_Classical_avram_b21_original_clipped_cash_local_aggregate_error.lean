-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b21_original_clipped_cash_local_aggregate_error
-- name    : AvramDividend.Classical.avram_b21_original_clipped_cash_local_aggregate_error
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:12:07.105512+00:00
-- url     : https://prove2.me/theorems/4f2ce7a4-ae22-4689-807e-8dceab61175b
-- title:
--   Original ruin-clipped finite-cap mixed Ito-Meyer aggregate gain with arbitrarily small initial-event error
-- statement:
--   For every original right-continuous initial-filtration event and compact stopped positive-clock reward, construct one locally integrable centered aggregate gain and an integrable signed physical Ito-Meyer error of arbitrarily small expected size. The reward has the true original Lévy source and exact closed-prefix Stieltjes dividend measure, clipped at ruin and the finite horizon.
-- source:
--   Avram Palmowski Pistorius Proposition 4(i) arXiv:math/0702893; original physical Gaussian/negative-jump stopped Ito-Meyer with eventwise localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b21_original_clipped_cash_local_aggregate_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (hκstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ k ω : WithTop ℝ≥0)))
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ k ω, H k ω =
      Real.exp (-(q * (κ k ω : ℝ))) *
        w (if κ k ω = 0 ∨
              (κ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω
          else riskProcess X x D (κ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ k (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
    ∀ ε : ℝ, 0 < ε →
      ∃ M Err : Ω → ℝ,
        IntegrableOn M (A ∩ {η : Ω | κ k η ≠ 0}) P ∧
        IntegrableOn Err (A ∩ {η : Ω | κ k η ≠ 0}) P ∧
        (∫ ω in A ∩ {η : Ω | κ k η ≠ 0}, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | κ k η ≠ 0})),
          H k ω ≤ w x + M ω + Err ω) ∧
        (∫ ω in A ∩ {η : Ω | κ k η ≠ 0}, Err ω ∂P) ≤ ε := by sorry
