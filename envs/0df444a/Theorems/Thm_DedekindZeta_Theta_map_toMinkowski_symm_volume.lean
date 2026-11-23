-- Prove2me | Theorems.Thm_DedekindZeta_Theta_map_toMinkowski_symm_volume
-- name    : DedekindZeta.Theta.map_toMinkowski_symm_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:19:42.500079+00:00
-- url     : https://prove2.me/theorems/4a69eede-1c32-469f-a704-c712b913aeb7
-- title:
--   Theta: map to Minkowski symm volume
-- statement:
--   Pushing the (Euclidean) Lebesgue measure of `minkowskiSpace K` back to the
--   mixed space along `(toMinkowski K).symm` multiplies it by `2 ^ r₂`: `toMixed` is
--   volume preserving while the `√2`-weighting on the `r₂` complex coordinates
--   scales volume by `(√2)^(2·r₂) = 2 ^ r₂`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1949-L1976
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1949-L1976

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open MeasureTheory

theorem DedekindZeta.Theta.map_toMinkowski_symm_volume :
    Measure.map (toMinkowski K).symm (volume : Measure (minkowskiSpace K))
      = ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K) • (volume : Measure (mixedSpace K)) := by sorry
