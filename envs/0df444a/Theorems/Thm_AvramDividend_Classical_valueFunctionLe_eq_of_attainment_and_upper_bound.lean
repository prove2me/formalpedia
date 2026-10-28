-- Prove2me | Theorems.Thm_AvramDividend_Classical_valueFunctionLe_eq_of_attainment_and_upper_bound
-- name    : AvramDividend.Classical.valueFunctionLe_eq_of_attainment_and_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:53:01.008095+00:00
-- url     : https://prove2.me/theorems/cc99fa8e-6774-4176-9909-6dbb1a289c67
-- title:
--   An attained capped dividend upper bound equals the capped optimal value
-- statement:
--   By the definition of the capped value function as a supremum, any capped admissible dividend policy has value no greater than the optimal capped value. If this policy attains a proposed upper bound and that proposed bound dominates the supremum, antisymmetry gives equality. This is a reusable elementary order-theoretic verification lemma supporting the final assembly of Avram, Palmowski and Pistorius Theorem 2 (optimal barrier strategy). It introduces no stochastic assumptions beyond the policy admissibility and uses the existing precise value-function definitions.
-- source:
--   Avram, Palmowski and Pistorius (2007), On the Optimal Dividend Problem for a Spectrally Negative Levy Process I, Theorem 2, value-function supremum comparison step.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.valueFunctionLe_eq_of_attainment_and_upper_bound
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mOmega}
    (X : SpectrallyNegativeLevy P F) (q x : Real)
    (C B : ENNReal) (D : NNReal -> Omega -> Real)
    (hD : IsAdmissibleLe X x C D)
    (hvalue : dividendValue X q x D = B)
    (hupper : valueFunctionLe X q C x <= B) :
    valueFunctionLe X q C x = B := by sorry
