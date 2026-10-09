-- Prove2me | Theorems.Thm_ActuarialValuation_multiStateTermCashflowPV_zero_cashflows
-- name    : ActuarialValuation.multiStateTermCashflowPV_zero_cashflows
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:19:13.718632+00:00
-- url     : https://prove2.me/theorems/4c3e3ab6-62e3-4af6-ba03-c12405d8a23e
-- title:
--   Zero benefit streams have zero PV
-- statement:
--   With no state or transition payments in any year, PV vanishes.
--
--   **Mathematical statement**
--
--   $$
--   b=c=0\Rightarrow V_n=0
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_multiStateTermCashflowPV
open MeasureTheory

namespace ActuarialValuation

theorem multiStateTermCashflowPV_zero_cashflows {S : Type*} [Fintype S] (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ) (v : ℝ) (n : ℕ)
  :
  multiStateTermCashflowPV μ P (fun _ _ _ => 0) (fun _ _ => 0) v n = 0 := by sorry

end ActuarialValuation
