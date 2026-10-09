-- Prove2me | Theorems.Thm_ActuarialValuation_twoStepTransition_assoc
-- name    : ActuarialValuation.twoStepTransition_assoc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:07:12.764303+00:00
-- url     : https://prove2.me/theorems/6c5b7959-e8cc-4199-afe8-8cd64e1bdcec
-- title:
--   Finite transition composition is associative
-- statement:
--   The Chapman–Kolmogorov operator composes associatively, even for arbitrary real-valued kernels.
--
--   **Mathematical statement**
--
--   $$
--   (PQ)R=P(QR)
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_twoStepTransition
open MeasureTheory

namespace ActuarialValuation

theorem twoStepTransition_assoc {S : Type*} [Fintype S] (P Q R : S → S → ℝ) (a d : S)
    :
    twoStepTransition (twoStepTransition P Q) R a d =
      twoStepTransition P (twoStepTransition Q R) a d := by sorry

end ActuarialValuation
