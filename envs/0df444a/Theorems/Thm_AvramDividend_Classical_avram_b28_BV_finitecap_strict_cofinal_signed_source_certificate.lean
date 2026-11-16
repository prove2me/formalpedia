-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b28_BV_finitecap_strict_cofinal_signed_source_certificate
-- name    : AvramDividend.Classical.avram_b28_BV_finitecap_strict_cofinal_signed_source_certificate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:50:33.050284+00:00
-- url     : https://prove2.me/theorems/d022c4c7-b4de-4295-8a0f-30294d9054e9
-- title:
--   Finite-cap bounded-variation original physical strict cofinal signed Stieltjes and compensated-jump source certificate
-- statement:
--   The finite-cap branch C<top of the original strict cofinal signed physical BV source ledger. Under the original Standing BV hypotheses, positive benchmark, HJB generator-gradient inequality and admissible dividends, construct a strictly pre-horizon cofinal sequence with original dividend cash and terminal survival payoff bounded by w(x) plus integrable nonpositive-mean signed martingale gains and vanishing positive L1 error. The top-cap branch is already supported by a separate Proved original-source certificate 0f7e5e67; this finite-cap obligation isolates the remaining spatial cap-contact and drift-envelope arguments.
-- source:
--   Prove2Me B28 original signed BV source 530dc3d8 and Proved topcap certificate 0f7e5e67; remaining genuine finite-cap original physical mesh obstruction, 15 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_b28_BV_finitecap_strict_cofinal_signed_source_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (hwpos : 0 < w x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∃ u : ℕ → ℝ,
      Monotone u ∧
      (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) ∧
      ∃ R J Err : ℕ → Ω → ℝ,
        (∀ n, Integrable (fun ω => R n ω + J n ω) P ∧
          (∫ ω, R n ω + J n ω ∂P) ≤ 0) ∧
        (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
        Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P)
          atTop (𝓝 (0 : ℝ)) ∧
        (∀ n, ∀ᵐ ω ∂P,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
           else 0) ≤
            w x + (R n ω + J n ω) + max (Err n ω) 0) := by sorry
