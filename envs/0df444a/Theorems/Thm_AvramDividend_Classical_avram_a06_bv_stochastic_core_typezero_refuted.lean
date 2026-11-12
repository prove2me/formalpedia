-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_bv_stochastic_core_typezero_refuted
-- name    : AvramDividend.Classical.avram_a06_bv_stochastic_core_typezero_refuted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:14:13.779192+00:00
-- url     : https://prove2.me/theorems/170f7b70-c1ce-4a26-a0d6-68b6e05fe7af
-- title:
--   Concrete universe-zero counterexample to bounded-variation A06 universal cash bound
-- statement:
--   For the universe of small types, the exact original A06 bounded variation cash inequality is false. A published original filtered finite-activity Standing BV source and a zero-cap violating dividend strategy refute this universal instance. This statement uses Type (universe zero) and does not assert universe-polymorphic refutation.
-- source:
--   Root A06 theorem 3296bf8a-aa23-478b-842f-104133415fdd. Uses verified concrete original-space source-existence 3281148e and verified original-hypothesis zero-cap violating witness 696ceb2d. The official direct-disproof endpoint cannot import theorem modules, so this proposed proved theorem exposes the negative proposition separately. This universe-zero version avoids improperly generalising a small-type witness to arbitrary universes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_bv_stochastic_core_typezero_refuted :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω]
      {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
      (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
      (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
      (w : ℝ → ℝ) (C : ℝ≥0∞)
      (hw_cont : ContinuousOn w (Ici 0))
      (hw_neg : ∀ y < 0, w y = 0)
      (hw_smooth : ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
      (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
      (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
      (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
      (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
      (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω))
      (hjump : ∀ ω (t : ℝ≥0),
        (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
            w (riskProcess X x D t ω -
              (rightLimit D t ω - D t ω)))
      (T : ℝ) (hT : 0 ≤ T),
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) := by sorry
