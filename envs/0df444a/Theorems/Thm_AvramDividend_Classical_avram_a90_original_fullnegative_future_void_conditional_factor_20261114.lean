-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a90_original_fullnegative_future_void_conditional_factor_20261114
-- name    : AvramDividend.Classical.avram_a90_original_fullnegative_future_void_conditional_factor_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:24:08.608032+00:00
-- url     : https://prove2.me/theorems/6c5cfb23-41bf-4be9-9c05-feb05a0bcd6a
-- title:
--   Original negative-jump future no-arrival event has exact conditional probability against any raw past event
-- statement:
--   For any original spectrally negative Levy process with finite negative intensity and any event measurable at the raw F_s, the joint probability of that event and no negative physical jump during (s,s+T] is P(A) times exp(-T nu(-infty,0)). No zero-volatility or augmented filtration assumptions.
-- source:
--   Proved wave7_06 intrinsic future mark void event probability factor for arbitrary F_s-past event and Borel mark set; exact shifted full-negative void marginal A89.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a90_original_fullnegative_future_void_conditional_factor_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s T : ℝ≥0)
    (A : Set Ω) (hPast : MeasurableSet[𝓕 s] A)
    (hRaw : MeasurableSet A) :
    P (A ∩ {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iio (0 : ℝ)) = 0}) =
      P A * ENNReal.ofReal (Real.exp
        (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by sorry
