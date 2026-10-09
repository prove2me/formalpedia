-- Prove2me | Theorems.Thm_ActuarialValuation_multiStateTermCashflowPV_zero_term
-- name    : ActuarialValuation.multiStateTermCashflowPV_zero_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:18:21.802055+00:00
-- url     : https://prove2.me/theorems/666d3a59-cb0f-4b11-9c6d-a8800863ae6d
-- title:
--   Zero-year contract has zero expected PV
-- statement:
--   The finite cashflow horizon is empty when n is zero.
--
--   **Mathematical statement**
--
--   $$
--   V_0=0
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_multiStateTermCashflowPV
open MeasureTheory

namespace ActuarialValuation

theorem multiStateTermCashflowPV_zero_term {S : Type*} [Fintype S] (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ)
  (b : ℕ → S → S → ℝ) (c : ℕ → S → ℝ) (v : ℝ) 
  :
  multiStateTermCashflowPV μ P b c v 0 = 0 := by sorry

end ActuarialValuation
