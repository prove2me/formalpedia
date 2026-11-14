-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a62_original_BV_strict_prehorizon_ruinclipped_expected_physical_supermartingale_budget
-- name    : AvramDividend.Classical.avram_bva_a62_original_BV_strict_prehorizon_ruinclipped_expected_physical_supermartingale_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T23:47:44.502047+00:00
-- url     : https://prove2.me/theorems/540d60bf-13b5-4eb8-bca7-a0e6bbba2365
-- title:
--   Original infinite-activity BV physical strict-prehorizon stopped stochastic cash plus prepayment value expected upper bound
-- statement:
--   For every standing spectrally negative bounded-variation Levy process with infinite negative jump activity, every admissible dividend control under the original candidate w hypotheses, and each positive deterministic r strictly earlier than T, the expectation of discounted dividend cash strictly before r and the surviving true prepayment reserve value at r is bounded above by initial candidate w(x). This is the sound strict-prehorizon stochastic source needed to derive the original A55 horizon budget by random localisation, Fatou and Proved left-limit terminal continuity. It uses the actual dividendMeasure and original ruinTime, no global L1 compensated martingale witness, no spatial strict interior mask, and no false postpayment-terminal equality at T.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a62_original_BV_strict_prehorizon_ruinclipped_expected_physical_supermartingale_budget
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
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ (r : ℝ≥0), 0 < r → (r : ℝ) < T →
      (∫⁻ ω, ENNReal.ofReal
        ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
         (if (r : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * (r : ℝ))) * w (riskProcess X x D r ω)
          else 0)) ∂P) ≤ ENNReal.ofReal (w x) := by sorry
