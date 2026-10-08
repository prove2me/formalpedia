-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_eq_barrierValue
-- name    : AvramDividend.Classical.zero_reflectedSupValue_eq_barrierValue
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:42:40.607259+00:00
-- url     : https://prove2.me/theorems/b83a725b-f7cf-4aef-8105-310d38d8cd46
-- title:
--   Discounted reflected supremum until zero-barrier ruin equals the scale derivative boundary candidate
-- statement:
--   At the degenerate zero reflection barrier, the discounted cumulative running supremum of the spectrally negative Lévy process up to its first strictly positive drawdown has expected value given by the a=0 scale-function boundary expression, using the correct one-sided derivative W'(0+) in EReal and the divE convention. This is an excursion-potential/fluctuation identity, independent of the deterministic reflection-equals-barrier-dividends lemma, and must handle the zero-time stopping endpoint and time-zero dividend atom. It does not import the published zero-barrier identity that it is intended to prove.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, reflected supremum equation (3.13) and the a=0 boundary convention; canonical ReflectionBarrier module.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem zero_reflectedSupValue_eq_barrierValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry

end AvramDividend.Classical
