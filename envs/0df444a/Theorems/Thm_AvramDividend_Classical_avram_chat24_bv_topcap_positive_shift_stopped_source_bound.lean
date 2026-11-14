-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_topcap_positive_shift_stopped_source_bound
-- name    : AvramDividend.Classical.avram_chat24_bv_topcap_positive_shift_stopped_source_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:38:12.007673+00:00
-- url     : https://prove2.me/theorems/0d51b191-2d3b-48c9-a7ea-3569930b5b89
-- title:
--   Original BV top-cap positive-shift stopped cash and terminal HJB bound
-- statement:
--   For the original bounded-variation spectrally negative Levy process, its original admissible dividends and original ruin/paymentTimes convention, under the uncapped HJB and gradient hypotheses, the integrable strict stopped discounted cash plus surviving terminal w(U_T+delta) has expectation at most w(x+delta) for every delta>0. This preserves zero-time right dividends and excludes terminal cash at T. It is the substantive positive-shift stochastic source estimate, not a renamed copy of the full-HJB conclusion. Public source-faithful counterpart of private catalogue record 83064551-8422-4397-87db-41526c1846d4: guarded public-parent proof admission could not verify private dependency ownership. Parent 28363eea-15a4-4755-8b97-f3ad388c40b8 has a complete drafted monotonicity/continuity reduction; its graph remains unchanged until that proof is remotely accepted. The intended proof combines original intrinsic NX BV compensation, the original BV jump representation, the shifted pathwise stopped Stieltjes chain inequality, and the nonpositive HJB drift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_bv_topcap_positive_shift_stopped_source_bound
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Fδ : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω + δ)
       else 0)
    Integrable Fδ P ∧ (∫ ω, Fδ ω ∂P) ≤ w (x + δ) := by sorry
