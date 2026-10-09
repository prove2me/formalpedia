-- Prove2me | Theorems.Thm_ActuarialValuation_finiteKernel_nonnegative
-- name    : ActuarialValuation.finiteKernel_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:03:15.808991+00:00
-- url     : https://prove2.me/theorems/e21a84ce-c5a1-4606-aca6-629ebe2fc280
-- title:
--   Every transition entry is nonnegative
-- statement:
--   Extracts the nonnegative entry property of a valid transition kernel.
--
--   **Mathematical statement**
--
--   $$
--   P_{ab}\ge0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
open MeasureTheory

namespace ActuarialValuation

theorem finiteKernel_nonnegative {S : Type*} [Fintype S] (P : S → S → ℝ) (hP : isFiniteMarkovKernel P) (a b : S)
    :
    0 ≤ P a b := by sorry

end ActuarialValuation
