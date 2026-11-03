-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat05_bv_drift_envelope_complement_core
-- name    : AvramDividend.Classical.avram_wave6_chat05_bv_drift_envelope_complement_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T10:47:09.93659+00:00
-- url     : https://prove2.me/theorems/c8770486-df9d-4592-b003-b5072a666878
-- title:
--   Source BV stopped HJB core confined to nontrivial drift-envelope complement
-- statement:
--   For a genuine original bounded-variation spectrally negative Levy process and all positive-cap canonical HJB verification hypotheses, isolate the regime in which the proved exact unconditional drift budget x+T*d exceeds the candidate upper bound w(x). The complementary regime x+T*d≤w(x) follows directly from the already Proved original complete Stieltjes discounted cash budget, including all payment atoms. This child retains the exact controlled expected full Stieltjes bound and all stochastic HJB assumptions; its remaining proof genuinely needs stopped C1 finite-variation Ito and compensated source jump estimates.
-- source:
--   Exact case split on x+T*X.drift≤w x in original positive-cap BV core ef7e6c20-a118-46f0-ac94-5b02204bba49. The established original source theorem 23ddd713-8f78-4c6f-b478-98e0a5b32c7c closes the envelope branch, with ENNReal.ofReal monotonicity. This child isolates the complementary branch requiring stochastic HJB calculus. An explicit parent proof bridge is required and publication alone does not link theorem graphs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat05_bv_drift_envelope_complement_core
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
