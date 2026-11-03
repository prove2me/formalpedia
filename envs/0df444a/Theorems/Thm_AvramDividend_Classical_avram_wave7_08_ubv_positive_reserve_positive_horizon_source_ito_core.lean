-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_ubv_positive_reserve_positive_horizon_source_ito_core
-- name    : AvramDividend.Classical.avram_wave7_08_ubv_positive_reserve_positive_horizon_source_ito_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T11:45:23.85921+00:00
-- url     : https://prove2.me/theorems/6004b387-9caa-4ee7-b466-2bf22d148505
-- title:
--   Positive-reserve positive-horizon source UBV controlled Ito-Meyer verification core
-- statement:
--   For the genuine original spectrally negative Levy source process on the same Ω,P and filtration, at strictly positive reserve and strictly positive finite horizon, prove the corrected UBV HJB bound for the complete discounted Stieltjes dividends. This isolates only the nontrivial positive-time branch after the already Proved exact zero-horizon source lemma. It retains the C² interior, original generator, source admissible control, jump condition, ruin convention, and nonnegative boundary condition. The missing step is original same-path mixed Gaussian and compensated small-jump Ito-Meyer localisation with complete dividend mass, followed by Fatou.
-- source:
--   Exact strict-positive-horizon case of canonical positive-start helper 5dfefcd2-8b97-415b-aebd-4ad77dcd29cb. Parent implication will use Proved zero-horizon theorem 3858a86b-eff8-46f1-b700-7ee855dad85a; this publication does not by itself create a graph edge or prove the parent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_08_ubv_positive_reserve_positive_horizon_source_ito_core
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
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
    (T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
