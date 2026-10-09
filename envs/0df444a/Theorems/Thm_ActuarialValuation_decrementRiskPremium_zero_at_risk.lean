-- Prove2me | Theorems.Thm_ActuarialValuation_decrementRiskPremium_zero_at_risk
-- name    : ActuarialValuation.decrementRiskPremium_zero_at_risk
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T23:29:27.625869+00:00
-- url     : https://prove2.me/theorems/4d102abe-3b92-4789-8afa-6a3316a96094
-- title:
--   Risk premium vanishes when every decrement pays the reserve
-- statement:
--   If the benefit for every exit cause equals the next reserve, the net amount at risk is zero.
--
--   **Mathematical statement**
--
--   $$
--   b_j=R_+\Rightarrow\Pi^{\rm risk}=0
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Chapter 7 §7.5, equations (7.5.1)-(7.5.5); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §8.8 multiple decrement models, https://doi.org/10.1017/CBO9780511800146.009

import Mathlib
import Definitions.Def_actuarial_decrementRiskPremium
open MeasureTheory

namespace ActuarialValuation

theorem decrementRiskPremium_zero_at_risk {J : Type*} [Fintype J] (q : J → ℝ) (v Rnext : ℝ)
  :
  decrementRiskPremium q (fun _ => Rnext) v Rnext = 0 := by sorry

end ActuarialValuation
