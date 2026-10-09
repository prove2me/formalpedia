-- Prove2me | Theorems.Thm_ActuarialValuation_finiteKernel_row_sum
-- name    : ActuarialValuation.finiteKernel_row_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:05:01.921012+00:00
-- url     : https://prove2.me/theorems/ab3653ad-1d44-476c-b43b-6a0237075039
-- title:
--   Every transition row sums to one
-- statement:
--   Extracts the normalisation of each row of a valid finite-state transition kernel.
--
--   **Mathematical statement**
--
--   $$
--   \sum_bP_{ab}=1
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
open MeasureTheory

namespace ActuarialValuation

theorem finiteKernel_row_sum {S : Type*} [Fintype S] (P : S → S → ℝ) (hP : isFiniteMarkovKernel P) (a : S)
    :
    (∑ b : S, P a b) = 1 := by sorry

end ActuarialValuation
