-- Prove2me | Theorems.Thm_AvramDividend_Classical_valueFunction_eq_of_attainment_and_upper_bound
-- name    : AvramDividend.Classical.valueFunction_eq_of_attainment_and_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:53:02.653828+00:00
-- url     : https://prove2.me/theorems/2cd0a663-a02c-4255-9fa4-413ea9ce1c09
-- title:
--   An attained unrestricted dividend upper bound equals the optimal value
-- statement:
--   By the definition of the unrestricted dividend value function as a supremum over admissible policies, the expected value of an admissible policy is a lower bound for the unrestricted supremum. If its value matches a candidate upper bound on that supremum, the two opposite inequalities imply equality. This is a reusable elementary order-theoretic verification lemma supporting the final assembly of Avram, Palmowski and Pistorius Theorem 2 (optimal barrier strategy). It introduces no stochastic assumptions beyond the policy admissibility and uses the existing precise value-function definitions.
-- source:
--   Avram, Palmowski and Pistorius (2007), On the Optimal Dividend Problem for a Spectrally Negative Levy Process I, Theorem 2, value-function supremum comparison step.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.valueFunction_eq_of_attainment_and_upper_bound
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mOmega}
    (X : SpectrallyNegativeLevy P F) (q x : Real)
    (B : ENNReal) (D : NNReal -> Omega -> Real)
    (hD : IsAdmissible X x D)
    (hvalue : dividendValue X q x D = B)
    (hupper : valueFunction X q x <= B) :
    valueFunction X q x = B := by sorry
