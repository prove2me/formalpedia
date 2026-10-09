-- Prove2me | Theorems.Thm_ActuarialValuation_transitionRewardValue_nonnegative
-- name    : ActuarialValuation.transitionRewardValue_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:10:44.392214+00:00
-- url     : https://prove2.me/theorems/fc051c38-bef8-40ad-967b-958c2b26a9b2
-- title:
--   Nonnegative cashflows have nonnegative values
-- statement:
--   A nonnegative discount factor and nonnegative next-state rewards yield nonnegative value.
--
--   **Mathematical statement**
--
--   $$
--   v,P,r,V_{\rm next}\ge0\Longrightarrow V\ge0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_transitionRewardValue
open MeasureTheory

namespace ActuarialValuation

theorem transitionRewardValue_nonnegative {S : Type*} [Fintype S] (P : S → S → ℝ) (hP : isFiniteMarkovKernel P) (v : ℝ)
    (hv : 0 ≤ v) (r next : S → ℝ)
    (hr : ∀ b, 0 ≤ r b) (hn : ∀ b, 0 ≤ next b) (a : S)
    :
    0 ≤ transitionRewardValue P v r next a := by sorry

end ActuarialValuation
