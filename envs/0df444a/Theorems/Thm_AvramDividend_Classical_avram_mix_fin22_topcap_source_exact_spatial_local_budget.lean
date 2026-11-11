-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_topcap_source_exact_spatial_local_budget
-- name    : AvramDividend.Classical.avram_mix_fin22_topcap_source_exact_spatial_local_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T10:16:21.417956+00:00
-- url     : https://prove2.me/theorems/c087c2cb-0d29-4169-a0c7-34d34febe362
-- title:
--   Original top-cap finite-jump mixed compact stopped conditional cash budget
-- statement:
--   The sole genuinely stochastic top-cap analytic input for the mixed finite-jump branch. Construct on the original Omega/measure/filtration the true cofinal spatial upper-exit clocks, their ruin/horizon-clipped bounded stops, and source-exact inclusive dividend cash/terminal rewards. Prove their measurability and integrability and, for each original right-continuous initial-filtration event, a uniform expected positive-clock reward inequality. The original Ito-Meyer ledger, rather than globally L1 Gaussian/jump cross noise, must establish this local event bound. Cofinality and local nonnegativity are available from previously Proved theorems. Use no unjustified absolute first moment of large negative marks. This supplies a complete sound reduction of top conditional reward parent d7c74804 via bridge 08bbefb0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin22_topcap_source_exact_spatial_local_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
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
    (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCtop : C = ⊤) :
    ∃ (S : ℕ → Ω → ℝ≥0∞) (σk : ℕ → Ω → ℝ≥0)
      (Fk : ℕ → Ω → ℝ),
      (∀ ω, Monotone (fun k => S k ω)) ∧
      (∀ᵐ ω ∂P, (⨆ k : ℕ, S k ω) = ⊤) ∧
      (∀ k ω, σk k ω = (min (σ ω : ℝ≥0∞) (S k ω)).toNNReal) ∧
      Measurable σ ∧
      (∀ k, Measurable (σk k)) ∧
      (∀ k ω, σk k ω ≤ σ ω) ∧
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (σk k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, Fk k ω =
        Real.exp (-(q * (σk k ω : ℝ))) *
          w (if σk k ω = 0 ∨
                (σk k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σk k ω) ω - rightLimit D (σk k ω) ω
          else riskProcess X x D (σk k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σk k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) ∧
      (∀ k, Measurable (Fk k)) ∧
      (∀ k, Integrable (Fk k) P) ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        ∀ k, (∫ ω in A ∩ {η : Ω | σk k η ≠ 0}, Fk k ω ∂P) ≤
          w x * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal) := by sorry
