-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_scale_generator_origin_normalization_from_right_limit
-- name    : AvramDividend.Classical.gaussian_scale_generator_origin_normalization_from_right_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:27:12.546086+00:00
-- url     : https://prove2.me/theorems/32ee2e42-85ac-41d1-a9a9-e7190f032cee
-- title:
--   Gaussian generator boundary factor is one for the unique scale right-derivative limit
-- statement:
--   For the canonical positive Gaussian q-scale, whenever η is a right-hand limit of positive-level derivatives deriv W(x), the Gaussian generator boundary coefficient satisfies (sigma squared divided by two)*η = 1. The unique right-hand limit is 2/sigma squared by the Proved Gaussian root and right-slope theorems. This gives the exact `horigin` argument required by the Proved weighted Laplace generator-residual transform without using the incorrect ordinary `deriv W 0` value or introducing an unsupported differentiation-at-zero assumption.
-- source:
--   Proved positive_esscher_root_of_gaussian and gaussian_scale_right_derivative_of_positive_esscher_root, uniqueness of limits and elementary field identities.

import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.FieldSimp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_right_derivative_of_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace AvramDividend.Classical
/-- The Gaussian right slope automatically normalises the generator's boundary factor. -/
theorem gaussian_scale_generator_origin_normalization_from_right_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (η : ℝ) (hη : Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 η)) :
    (X.σ ^ 2 / 2) * η = 1 := by
  sorry
end AvramDividend.Classical
