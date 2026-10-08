-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator
-- name    : AvramDividend.Classical.vcstar_hjb_above_cstar_of_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:33:42.04725+00:00
-- url     : https://prove2.me/theorems/e1d50a0b-1093-42ad-a06b-f712f05608fe
-- title:
--   HJB equality strictly above c-star from the generator inequality
-- statement:
--   Above the barrier, the candidate value is affine with derivative one. Consequently the marginal-dividend term of the HJB maximum equals zero. The supplied generator inequality gives a nonpositive generator term, hence the full maximum is zero and the generator integral is convergent. This packages exactly the above-barrier HJB input for Theorem 2(ii).
-- source:
--   Avram, Palmowski and Pistorius (2007), Theorem 2(ii), generator condition above c* and HJB identity (5.8).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_hjb_above_cstar_of_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  sorry
end AvramDividend.Classical
