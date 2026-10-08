-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:09:41.911594+00:00
-- url     : https://prove2.me/theorems/bced81f2-1208-4b81-ab75-b3c77418fd4a
-- title:
--   C1 scale-function regularity in the bounded-variation absolutely-continuous Lévy case
-- statement:
--   In the bounded-variation branch, absolute continuity of the Lévy measure makes the positive jump-magnitude tail kernel continuous away from zero. Combined with the positive shifted renewal representation of the q-scale function, the convolution-density series for the renewal measure converges locally uniformly on every compact subset of (0,∞), giving a continuously differentiable tilted scale function and hence W∈C1(0,∞). This is the only genuinely new subcase needed for the absolutely-continuous branch once the proved unbounded-variation Gaussian/infinite-jump dichotomy is used.
-- source:
--   Avram, Palmowski, Pistorius (2007), condition (3.3); Chan, Kyprianou, Savov (2011), smoothness of scale functions; local derivation BV_SHIFTED_POSITIVE_RENEWAL_20261006.md.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry
