-- Prove2me | Theorems.Thm_ActuarialValuation_twoStepTransition_kernel
-- name    : ActuarialValuation.twoStepTransition_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:06:31.344226+00:00
-- url     : https://prove2.me/theorems/1a76e1c8-f799-4911-8aa3-7b9b18bdfcdf
-- title:
--   Composition of stochastic kernels is stochastic
-- statement:
--   The two-step transition is itself a valid finite-state Markov kernel.
--
--   **Mathematical statement**
--
--   $$
--   P,Q\text{ stochastic}\Longrightarrow PQ\text{ stochastic}
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_twoStepTransition
open MeasureTheory

namespace ActuarialValuation

theorem twoStepTransition_kernel {S : Type*} [Fintype S] (P Q : S → S → ℝ)
    (hP : isFiniteMarkovKernel P) (hQ : isFiniteMarkovKernel Q)
    :
    isFiniteMarkovKernel (twoStepTransition P Q) := by sorry

end ActuarialValuation
