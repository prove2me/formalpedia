-- Prove2me | Theorems.Thm_ActuarialValuation_futureTermLoss_integrable
-- name    : ActuarialValuation.futureTermLoss_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:51:00.943457+00:00
-- url     : https://prove2.me/theorems/a39c2e42-bff4-49c4-9c6b-b8d54bccf6d2
-- title:
--   Finite-term future loss is integrable
-- statement:
--   Measurability and finite discounting give integrability without bounded lifetime support.
--
--   **Mathematical statement**
--
--   $$
--   L_{n,t}\in L^1(P)
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_futureTermLossPV
open MeasureTheory

namespace ActuarialValuation

theorem futureTermLoss_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n t : ℕ)
    (b π : ℝ)
    :
    Integrable (futureTermLossPV K v n t b π) P := by sorry

end ActuarialValuation
