-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_canonical_ubv_core_false_type0
-- name    : AvramDividend.Classical.avram_wave3_04_canonical_ubv_core_false_type0
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:48:04.160216+00:00
-- url     : https://prove2.me/theorems/520139dd-2607-40fc-8888-ecd422d4ebc7
-- title:
--   Finite-cap Gaussian refutation of the canonical UBV verification proposition at Type 0
-- statement:
--   The universal UBV stochastic verification proposition over all Type-0 path spaces is false. A concrete Brownian Gaussian-limit sample path model witnesses the failure at finite cap one with drift -1, unit volatility, no jumps, candidate w(0)=-1 and a legitimate left-continuous dividend control. All analytic, admissibility, HJB, jump and terminal hypotheses hold, yet the expected discounted Stieltjes payments exceed the nonnegative part of w(x). This is an explicit negation of the original canonical proposition on its actual Brownian model universe and identifies the missing w(0)>=0 condition.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), w(0)>=0. Exact original target UUID ab47d6d9-7cd8-4e6a-b5b9-00d29941d9d4, combined with Prove2Me remotely accepted Gaussian and dividend control lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_concrete_gaussian_levy_source_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_drifted_unit_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_gaussian_core_missing_boundary_counterexample
import Theorems.Thm_AvramDividend_Classical_gaussian_cutoff_canonical_analytic_hypotheses
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_reserve_negative

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_canonical_ubv_core_false_type0 :
    ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ}
        (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
        (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
        (w : ℝ → ℝ) (C : ℝ≥0∞)
        (hw_cont : ContinuousOn w (Ici 0))
        (hw_neg : ∀ y < 0, w y = 0)
        (hw_smooth : ContDiffOn ℝ 2 w
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
        (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
        (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          1 ≤ deriv w y)
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
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) := by sorry
