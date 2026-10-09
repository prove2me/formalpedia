-- Prove2me | Theorems.Thm_ActuarialValuation_twoStepTransition_nonnegative
-- name    : ActuarialValuation.twoStepTransition_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:05:30.360842+00:00
-- url     : https://prove2.me/theorems/3841c8ab-21da-43f4-95a2-f3b08f9c715d
-- title:
--   Composed transition entries are nonnegative
-- statement:
--   Every term of the finite Chapman–Kolmogorov composition is nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   (PQ)_{ac}\ge0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_twoStepTransition
open MeasureTheory

namespace ActuarialValuation

theorem twoStepTransition_nonnegative {S : Type*} [Fintype S] (P Q : S → S → ℝ)
    (hP : isFiniteMarkovKernel P) (hQ : isFiniteMarkovKernel Q) (a c : S)
    :
    0 ≤ twoStepTransition P Q a c := by sorry

end ActuarialValuation
