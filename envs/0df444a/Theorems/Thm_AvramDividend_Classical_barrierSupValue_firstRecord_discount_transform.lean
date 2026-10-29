-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_firstRecord_discount_transform
-- name    : AvramDividend.Classical.barrierSupValue_firstRecord_discount_transform
-- status  : Open
-- author  : @WillR
-- created : 2026-10-29T00:22:08.912982+00:00
-- url     : https://prove2.me/theorems/e959aa44-3edf-4231-9722-416c9c4817f2
-- title:
--   q-discounted survival transform of record levels before reflected drawdown ruin
-- statement:
--   For a spectrally negative Levy process satisfying the standing assumptions, q > 0, a > 0, and a q-scale function W with W(a) > 0 and W'(a) > 0, the expected q-discounted indicator that the running supremum reaches level r before the reflected drawdown exceeds a is exp(-r W'(a)/W(a)) for every r > 0. This is the inverse-record-clock form of the excursion compensation identity underlying the reflected dividend formula.
-- source:
--   Avram, Palmowski and Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Proposition 1 equations (3.12)-(3.13); the excursion compensation and reflected exit calculation are developed in Avram, Kyprianou and Pistorius, Exit problems for spectrally negative Levy processes and applications to (Canadized) Russian options, Annals of Applied Probability 14 (2004), Theorem 1 and proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_firstRecord_discount_transform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (hWa : 0 < W a)
    (hderiv : 0 < deriv W a) :
    ∀ r : ℝ≥0, 0 < (r : ℝ) →
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : (r : ℝ) < runningSup X t ω), (t : ℝ≥0∞)) <
            barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : (r : ℝ) < runningSup X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) =
        ENNReal.ofReal (Real.exp (-((r : ℝ) * deriv W a / W a))) := by sorry
