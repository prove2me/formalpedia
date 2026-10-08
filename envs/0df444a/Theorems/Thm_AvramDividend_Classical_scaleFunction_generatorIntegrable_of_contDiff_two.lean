-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrable_of_contDiff_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T10:07:26.817982+00:00
-- url     : https://prove2.me/theorems/a977868a-dcb0-47f7-b1bc-66e7454ceb8d
-- title:
--   C2 scale functions have an integrable compensated Levy generator jump term locally
-- statement:
--   Pure analytic jump-integrability lemma. A q-scale function vanishes on the negative half-line and is nonnegative and monotone on the positive half-line. If it is C2 on an open interval (0,a) containing x, then the compensated negative-jump generator integrand is integrable at x for any spectrally negative Levy measure satisfying the mission's standard second-moment Levy condition. Split jumps into a neighbourhood of zero, where Taylor's remainder is O(y^2), and jumps bounded away from zero, where the Levy measure has finite mass and monotonicity bounds W(x+y).
-- source:
--   Standard Levy-generator estimate; used in the proof of Lemma 4 of Avram, Palmowski and Pistorius (2007).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrable_of_contDiff_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    X.GeneratorIntegrable W x := by sorry

end AvramDividend.Classical
