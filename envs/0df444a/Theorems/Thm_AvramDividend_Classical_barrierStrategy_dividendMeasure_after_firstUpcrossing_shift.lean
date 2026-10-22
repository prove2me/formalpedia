-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_after_firstUpcrossing_shift
-- name    : AvramDividend.Classical.barrierStrategy_dividendMeasure_after_firstUpcrossing_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T11:46:12.936431+00:00
-- url     : https://prove2.me/theorems/3718616c-a366-4b38-bf0b-b14e98b527d1
-- title:
--   After the first up-crossing of the barrier gap the dividend measure of the barrier strategy is the shifted dividend measure of the running supremum of the shifted process
-- statement:
--   The strong Markov step of the barrier strategy value identity, in its Lebesgue-Stieltjes measure form. Let u be the first time the process X strictly crosses the level a - x above the starting capital x, so that the barrier strategy has paid nothing yet and the reserve has just reached the barrier level a. After that time the barrier strategy coincides, pathwise, with the running supremum of the shifted process X_{u + .} - X_u started from the reserve a. This statement says that the Lebesgue-Stieltjes measure of the dividends paid by the barrier strategy in the time window (u, u + t] is exactly the Lebesgue-Stieltjes measure of the running supremum dividends of the shifted process in the window (0, t], with the shift t ↦ u + t understood as the time change. Together with the discount factorisation e^{-q (u + t)} = e^{-q u} e^{-q t} this is the ingredient that turns the dividend value of the barrier strategy into the discounted probability of the up-crossing occurring before ruin times the barrier dividend value of the shifted process, which is the factorisation of Proposition 1 of Avram, Palmowski and Pistorius.
-- source:
--   The strong Markov property of a spectrally negative Levy process applied to the Lebesgue-Stieltjes dividend measure of the barrier strategy, at the first up-crossing of the barrier gap. The pathwise counterpart is the Proved theorem barrierStrategy_after_firstUpcrossing_shift, which identifies the barrier strategy after the up-crossing with the running supremum of the shifted path. The measure-theoretic step asserted here, that the dividend measure is carried over by that shift, is the ingredient needed for the factorisation barrierStrategy_value_eq_killed_exit_mul_supValue of Proposition 1 of Avram, Palmowski and Pistorius, arXiv:math/0702893v1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_dividendMeasure_after_firstUpcrossing_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)) :
    ∀ (t : ℝ≥0),
      (dividendMeasure (barrierStrategy X x a) ω) (Ioc u (u + t)) =
        (dividendMeasure (runningSup X) ω) (Ioc 0 t) := by sorry
