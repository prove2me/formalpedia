-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_bv_stochastic_core_positive_cap
-- name    : AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_core_positive_cap
-- status  : Open
-- author  : @WillR
-- created : 2026-10-26T23:19:43.061993+00:00
-- url     : https://prove2.me/theorems/ef7e6c20-a118-46f0-ac94-5b02204bba49
-- title:
--   Positive-cap BV stopped HJB verification with nonnegative initial reserve and value
-- statement:
--   For a nonzero cap and nonnegative initial reserve, a bounded-variation spectrally negative Lévy process with positive discount and a continuously differentiable HJB supersolution dominates every capped admissible strategy's expected discounted complete Stieltjes dividends up to a finite horizon, provided its terminal pre-ruin values are nonnegative and its value drops dominate lump-sum dividends. The statement includes the continuous dividend component and the time-zero Stieltjes atom.
-- source:
--   Source-faithful stopped BV branch of Avram–Palmowski–Pistorius (2007), Proposition 4(i), for the existing canonical local_verification root (UUID f318a688-56f8-459d-865b-f64d192f9630). Repairs the zero-cap and missing initial nonnegativity hypotheses in the published standalone BV core (UUID 3296bf8a-aa23-478b-842f-104133415fdd). To bridge to the canonical local_verification, derive the jump inequality from the existing HJB gradient lemma, prove this finite-horizon stochastic inequality through BV change of variables, then apply established Fatou and value-function supremum lemmas. New theorem publication does not itself correct the defective old target or add a dependency edge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_core_positive_cap
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
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
