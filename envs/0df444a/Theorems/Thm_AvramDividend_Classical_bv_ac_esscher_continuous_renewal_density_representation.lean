-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_continuous_renewal_density_representation
-- name    : AvramDividend.Classical.bv_ac_esscher_continuous_renewal_density_representation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-23T16:26:09.908302+00:00
-- url     : https://prove2.me/theorems/17bc0aad-807f-4e33-82d9-b8a65d2b6166
-- title:
--   Continuous Esscher renewal-density representation for BV absolutely continuous Lévy scale functions
-- statement:
--   Under the standing hypotheses, bounded variation and absolute continuity of the Lévy measure, there is a positive Esscher q-root and a continuous interval-integrable density on the positive axis whose integrated cumulative equals the tilted q-scale function. Proving this requires renewal-kernel convolution density and locally uniform geometric-series convergence, and supplies exactly the missing non-calculus part of BV smooth fit.
-- source:
--   Avram, Palmowski and Pistorius (2007), BV q-scale function and condition (3.3); Chan, Kyprianou and Savov (2011), scale-function smoothness from renewal equations.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem bv_ac_esscher_continuous_renewal_density_representation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ c : ℝ) (f : ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧
      ContinuousOn f (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x =
          c + ∫ y in (0 : ℝ)..x, f y) := by sorry
end AvramDividend.Classical
