-- Prove2me | Theorems.Thm_ActuarialValuation_futureTermPremium_nonnegative
-- name    : ActuarialValuation.futureTermPremium_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:50:22.848573+00:00
-- url     : https://prove2.me/theorems/5f4f5727-5337-4fbd-afd7-62671f3371d8
-- title:
--   Future premium has nonnegative PV
-- statement:
--   Every premium indicator contributes a nonnegative amount.
--
--   **Mathematical statement**
--
--   $$
--   v\ge0\Longrightarrow Y_{n,t}\ge0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_futureTermPremiumPV
open MeasureTheory

namespace ActuarialValuation

theorem futureTermPremium_nonnegative {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω)
    (hv : 0 ≤ v)
    :
    0 ≤ futureTermPremiumPV K v n t ω := by sorry

end ActuarialValuation
