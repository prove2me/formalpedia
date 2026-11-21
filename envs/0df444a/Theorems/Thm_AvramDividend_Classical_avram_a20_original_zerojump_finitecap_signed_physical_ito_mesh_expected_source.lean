-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_zerojump_finitecap_signed_physical_ito_mesh_expected_source
-- name    : AvramDividend.Classical.avram_a20_original_zerojump_finitecap_signed_physical_ito_mesh_expected_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T07:34:35.45704+00:00
-- url     : https://prove2.me/theorems/282e519a-dbfe-460e-86bd-59330f393f95
-- title:
--   Exact original finitecap Gaussian stopped physical Ito ledger with signed vanishing mean residual
-- statement:
--   For each original finitecap stopped real HJB reward F_k with inclusive ruin-clock dividend Stieltjes cash, construct genuine finite Gaussian physical Ito/Taylor grid sums Q_j built from original zero-jump Lévy process X and its centered stopped increments, and signed errors E_j. Require integrable zero-mean physical sums and integrable signed errors with vanishing expected values; prove each finite-grid cash inequality F_k <= w(x)+Q_j+E_j. This source retains every original admissibility and HJB hypothesis and isolates the substantive original physical Ito generator, stochastic martingale, cap kink and ruin-contact estimates. It is an alternative mean-based route requiring no a.e mesh error convergence and no arbitrary source budget or cash inequality without finite-grid evidence.
-- source:
--   Avram original finite-cap Gaussian stopped verification, finite signed physical X-increment Taylor ledger, terminal postpayment and inclusive Stieltjes cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_original_zerojump_finitecap_signed_physical_ito_mesh_expected_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
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
    (hν : X.ν = 0) (hFinite : C ≠ ⊤) :
    ∀ k, ∃ (S : ℕ → Finset ℕ)
      (τg : ℕ → ℕ → Ω → ℝ≥0)
      (h : ℕ → ℕ → ℝ≥0)
      (G H : ℕ → ℕ → Ω → ℝ)
      (Q E : ℕ → Ω → ℝ),
      (∀ j ω, Q j ω =
        ∑ i ∈ S j,
          (let Z : ℝ := (X.X (τg j i ω + h j i) ω -
              ((τg j i ω + h j i : ℝ≥0) : ℝ) * X.c) -
              (X.X (τg j i ω) ω - (τg j i ω : ℝ) * X.c)
           G j i ω * Z + H j i ω *
              (Z ^ 2 - ((h j i : ℝ) * X.σ ^ 2)))) ∧
      (∀ j, Integrable (Q j) P) ∧
      (∀ j, (∫ ω, Q j ω ∂P) = 0) ∧
      (∀ j, Integrable (E j) P) ∧
      Tendsto (fun j => ∫ ω, E j ω ∂P)
        Filter.atTop (nhds (0 : ℝ)) ∧
      (∀ j, ∀ᵐ ω ∂P,
        F k ω ≤ w x + Q j ω + E j ω) := by sorry
