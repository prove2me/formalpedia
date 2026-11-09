-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_original_strict_source_centered_witness
-- name    : AvramDividend.Classical.avram_ubv_finite12_original_strict_source_centered_witness
-- status  : Open
-- author  : @WillR
-- created : 2026-11-08T22:43:16.4107+00:00
-- url     : https://prove2.me/theorems/d1caa4aa-f44e-406b-b756-f6521d6a544f
-- title:
--   Original finite-cap Gaussian stopped strict prepayment reward conditional martingale domination
-- statement:
--   For the original zero-jump non-BV Lévy process, original finite-cap admissible dividend strategy and each bounded original stopping clock, the positive-clock strict prepayment stopped terminal plus strictly earlier Stieltjes dividend cash (with zero-clock branch exactly w(x)) is bounded a.e. by w(x) plus an integrable martingale residual initially conditionally centred in the original filtration. Unlike the source reward F, this strict ledger excludes postpayment right jumps and closed horizon cash; the Proved endpoint bridge c9478067 proves F is pointwise below it. The remaining substantive proof is the physical stopped compact-localised Gaussian C2 Ito inequality with cap/ruin boundary and last-cell control.
-- source:
--   UBV-FINITE12 root-connected strict-source reduction of Open a338c453 using newly Proved endpoint c9478067; source not equivalent to original F because its terminal uses prepayment and the cash interval is strict.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite12_original_strict_source_centered_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
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
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, ∃ M : Ω → ℝ,
      Integrable M P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) ∧
      (∀ᵐ ω ∂P,
        (if σ k ω = 0 then w x else
          Real.exp (-(q * (σ k ω : ℝ))) *
            w (riskProcess X x D (σ k ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) ≤ w x + M ω) := by sorry
