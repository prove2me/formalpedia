-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_local_regularity
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_of_local_regularity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T10:10:26.13198+00:00
-- url     : https://prove2.me/theorems/7e22f7ff-32dc-4d06-a01d-ec09d15973ec
-- title:
--   Killed q-scale martingale plus Ito gives the local generator equation
-- statement:
--   Barrier-independent stochastic core of Lemma 4. The q-scale function is q-harmonic for X killed on entering the negative half-line: exp(-q(t∧T^-_0)) W(X_{t∧T^-_0}) is a martingale. On a positive interval (0,a), assume the generator jump term is integrable and the regularity required by the appropriate Levy-Ito formula: C1 in the bounded-variation case, or C2 in the unbounded-variation case. Applying Ito to the stopped killed martingale identifies its finite-variation drift as (Gamma W-qW) dt, so the drift must vanish pointwise on the interval.
-- source:
--   Avram, Palmowski and Pistorius (2007), equation (3.7) and Proof of Lemma 4, p. 21; the paper cites Sato Theorems 31 and 32 for the two Ito variants.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_of_local_regularity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x)
    (hreg :
      (X.BoundedVariation ∧ ContDiffOn ℝ 1 W (Ioo 0 a)) ∨
      (¬ X.BoundedVariation ∧ ContDiffOn ℝ 2 W (Ioo 0 a))) :
    ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
