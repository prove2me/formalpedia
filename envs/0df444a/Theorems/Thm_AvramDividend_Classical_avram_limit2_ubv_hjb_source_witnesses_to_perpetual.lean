-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_ubv_hjb_source_witnesses_to_perpetual
-- name    : AvramDividend.Classical.avram_limit2_ubv_hjb_source_witnesses_to_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T07:50:12.104267+00:00
-- url     : https://prove2.me/theorems/9057f9b2-92cd-4db1-82b7-2bfe803f331d
-- title:
--   UBV original source witness martingales under HJB imply genuine perpetual dividend bound
-- statement:
--   For the original unbounded-variation spectrally negative Levy process, the canonical HJB max equation directly supplies the derivative lower bound on the positive capped interior. Uniform positive natural-horizon source witnesses consisting of the exact stopped clock, postpayment or ruin reserve, genuine closed Iic stopped discounted Stieltjes cash, genuine source terminal, an integrable centred martingale and two integrable nonpositive-drift terms then imply the full perpetual dividendValue upper bound via the Proved LIMIT-1 UBV source-to-value theorem. Source martingale witnesses and their bounds remain explicit hypotheses. There is no equality-in-law, omission of initial or horizon atoms, or unjustified terminal vanishing.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_uniform_positive_source_to_dividendValue

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_ubv_hjb_source_witnesses_to_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hEvidence : ∀ k : ℕ, 0 < k →
      ∃ (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ),
        (∀ ω, τ ω =
          (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal) ∧
        Measurable (fun ω => (τ ω : ℝ)) ∧
        (∀ ω, W ω = if τ ω = 0 ∨
          (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) ∧
        (∀ ω, Cash ω = (∫⁻ s in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) ∧
        (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
        Integrable Cash P ∧
        (∃ M G H : Ω → ℝ,
          Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
          (∫ ω, M ω ∂P) = 0 ∧
          (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
          (∀ᵐ ω ∂P, Term ω + Cash ω ≤
            w x + M ω + G ω + H ω))) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
