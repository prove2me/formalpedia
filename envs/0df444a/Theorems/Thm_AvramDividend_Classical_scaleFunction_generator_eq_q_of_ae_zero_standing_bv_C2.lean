-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_ae_zero_standing_bv_C2
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_of_ae_zero_standing_bv_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T10:55:51.049002+00:00
-- url     : https://prove2.me/theorems/a18b3e5c-4177-40b6-b447-67a758ac22fd
-- title:
--   Almost-everywhere q-harmonicity implies pointwise q-harmonicity in the standing BV C2 regime
-- statement:
--   Under the standing bounded-variation Lévy assumptions, when W is a C2 q-scale function on (0,a), its generator residual has already been proved continuous on each compact interior interval. If ΓW−qW vanishes Lebesgue-almost everywhere on (0,a), it therefore vanishes pointwise throughout (0,a). This replaces the final pointwise stochastic identification by an a.e. identity as the exact remaining target.
-- source:
--   Already verified compact residual regularity, compact-to-open continuity, and local almost-everywhere zero support upgrade.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_of_ae_zero_standing_bv_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hae : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0) :
    ∀ x ∈ Ioo 0 a, X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
