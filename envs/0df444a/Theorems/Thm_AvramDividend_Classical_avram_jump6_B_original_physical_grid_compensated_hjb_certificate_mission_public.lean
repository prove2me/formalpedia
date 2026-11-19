-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_grid_compensated_hjb_certificate_mission_public
-- name    : AvramDividend.Classical.avram_jump6_B_original_physical_grid_compensated_hjb_certificate_mission_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T16:17:28.119283+00:00
-- url     : https://prove2.me/theorems/c12a10fa-529a-4cfd-8062-5257a1b69b98
-- title:
--   Mission public: True original stopped physical-grid Ito-Meyer discounted source and closed-Iic dividend mesh certificate for infinite jump activity
-- statement:
--   This is the actual analytic source obligation behind the mixed infinite-activity five-component ledger. For every subordinate stopping clock of the original process, produce deterministic physical grids, the exact X.X/rightLimit D discounted finite-grid Source and Dividend functions, an L1-centred original martingale terminal that cancels at zero clock, and nonpositive generator/dividend pathwise residuals with the exact source finite-grid convergence and closed-Iic payment error bound. The conclusion specifies the real physical-grid functions used in the already Proved source-asymptotic dividend inequality 193e1b1b. There are no imported open theorems, no surrogate process, and no finite-jump-activity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_physical_grid_compensated_hjb_certificate_mission_public
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
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ k : ℕ,
      let Cash : Ω → ℝ := fun ω : Ω =>
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      ∃ (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
        (Source Dividend : ℕ → Ω → ℝ) (Mc G R : Ω → ℝ),
        (∀ j, Monotone (u j)) ∧
        (∀ j, u j 0 = 0) ∧
        (∀ ω, ∀ᶠ j in atTop, σ k ω ≤ u j (m j)) ∧
        (∀ ω, (σ k ω : ℝ≥0∞) ≤ ruinTime X x D ω) ∧
        (∀ n ω, Source n ω =
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (σ k ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      ∑ i ∈ Finset.range (m n),
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))) ∧
        (∀ n ω, Dividend n ω =
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (σ k ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let pre : Prop := σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω
      (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (m n),
          ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
            E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
            E (v (i + 1)) *
              (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
            E (v (i + 1)) *
              (w (Y (v (i + 1))) -
                w (riskProcess X x D (v (i + 1)) ω)))) +
        (if pre then 0 else E (σ k ω) *
          (w (riskProcess X x D (σ k ω) ω) - w (Y (σ k ω)))) -
        Source n ω) ∧
        Integrable Mc P ∧ Integrable G P ∧ Integrable R P ∧
        (∫ ω, Mc ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, σ k ω = 0 → Mc ω = 0) ∧
        (∀ᵐ ω ∂P, G ω ≤ 0) ∧
        (∀ᵐ ω ∂P, R ω ≤ 0) ∧
        (∀ᵐ ω ∂P, Tendsto (fun j => Source j ω) atTop (𝓝 (Mc ω + G ω))) ∧
        (∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, Dividend n ω + Cash ω ≤ R ω + ε) := by sorry
