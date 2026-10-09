-- Prove2me | Theorems.Thm_ActuarialValuation_multiStateTermCashflowPV_scale
-- name    : ActuarialValuation.multiStateTermCashflowPV_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:23:26.748883+00:00
-- url     : https://prove2.me/theorems/d4767558-d93e-4a72-9719-e5d01a9f0e7d
-- title:
--   Scaling all benefits scales contract PV
-- statement:
--   Linearity of finite sums means a common benefit scale a multiplies total PV.
--
--   **Mathematical statement**
--
--   $$
--   V_n(ab,ac)=aV_n(b,c)
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_multiStateTermCashflowPV
open MeasureTheory

namespace ActuarialValuation

theorem multiStateTermCashflowPV_scale {S : Type*} [Fintype S] (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ)
  (b : ℕ → S → S → ℝ) (c : ℕ → S → ℝ) (v : ℝ) (n : ℕ) (a : ℝ)
  :
  multiStateTermCashflowPV μ P
    (fun k i j => a * b k i j) (fun k i => a * c k i) v n =
      a * multiStateTermCashflowPV μ P b c v n := by sorry

end ActuarialValuation
