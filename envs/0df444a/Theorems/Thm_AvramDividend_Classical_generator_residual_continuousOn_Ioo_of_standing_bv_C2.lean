-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioo_of_standing_bv_C2
-- name    : AvramDividend.Classical.generator_residual_continuousOn_Ioo_of_standing_bv_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:46:05.99762+00:00
-- url     : https://prove2.me/theorems/4c8f36e7-1f98-41eb-8377-2109495a4c66
-- title:
--   Standing bounded-variation C2 generator residual is continuous throughout the positive interval
-- statement:
--   The standing BV assumptions force Lévy atomlessness and continuity of the compensated jump generator on compact subintervals. The residual ΓW−qW has already been proved continuous on every compact subinterval [l,u] of the C2 region (0,a). The compact-to-open continuity bridge upgrades this to continuity of the residual on all (0,a). This helps promote a future almost-everywhere q-harmonicity theorem to the desired pointwise identity.
-- source:
--   Accepted compact Lévy-generator residual continuity and compact-to-open continuity, Avram Dividend mission.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_continuousOn_Ioo_of_standing_bv_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x)
      (Ioo 0 a) := by sorry

end AvramDividend.Classical
