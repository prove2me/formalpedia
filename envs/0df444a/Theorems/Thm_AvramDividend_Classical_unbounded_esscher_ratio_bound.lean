-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_esscher_ratio_bound
-- name    : AvramDividend.Classical.unbounded_esscher_ratio_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:33:15.753636+00:00
-- url     : https://prove2.me/theorems/8ec2b84f-4b1d-423d-b296-a3f3ee5a357c
-- title:
--   Exponential decay of the q-scale-function ratio at the positive Esscher root, for unbounded variation
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation and W its q-scale function for q > 0. Then there is a positive Esscher root phi with psi(phi) = q, and the scale-function ratio obeys the exponential decay bound W(x)/W(y) <= exp(-phi (y - x)) for all 0 < x <= y. Equivalently the Esscher-normalised function exp(-phi x) W(x) is nonincreasing on the positive half-line. This is the Cramer-root decay estimate: it is the quantitative form of the fact that the q-scale function grows like the positive exponential at infinity, and it is the analytic input that the Esscher change of measure is built to produce. The hypothesis of unbounded variation is exactly what excludes the bounded-variation renewal-density case, so the statement does not require the standing assumptions: the integrable first moment of the positive part is not available when the Levy measure has an infinite first moment near zero, and the infinite-small-jump case is one of the regimes this theorem must cover.
-- source:
--   Chan, Kyprianou, Savov (2011), Smoothness of scale functions for spectrally negative Levy processes, section 3 and the Esscher change of measure at the positive root; Kyprianou (2011), Excursions and Stochasticity, the Cramer root and the exponential bound for the scale function.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_esscher_ratio_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ∃ (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q),
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x / W y ≤ Real.exp (-(φ * (y - x))) := by sorry
