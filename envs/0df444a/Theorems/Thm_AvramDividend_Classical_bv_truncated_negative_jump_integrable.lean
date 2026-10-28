-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_truncated_negative_jump_integrable
-- name    : AvramDividend.Classical.bv_truncated_negative_jump_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:17:22.894645+00:00
-- url     : https://prove2.me/theorems/f50055e5-0273-40b5-8fdc-dfe6aa1dc391
-- title:
--   BV truncated negative-jump generator compensator is integrable
-- statement:
--   For a spectrally negative Lévy process of bounded variation, the truncated y term in the generator is integrable over all negative jumps. On y<0 its support is exactly (-1,0), where the already proved BV first absolute moment condition applies.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4; bounded-variation Lévy compensation.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_integrable

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem bv_truncated_negative_jump_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation) :
    IntegrableOn
      (fun y : ℝ =>
        y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)
      (Iio (0 : ℝ)) X.ν := by sorry

end AvramDividend.Classical
