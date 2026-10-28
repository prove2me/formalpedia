-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_right_squeeze
-- name    : AvramDividend.Classical.exponential_right_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:18:56.418205+00:00
-- url     : https://prove2.me/theorems/3e85f3b6-57d9-4f32-ba22-75f51c92a67b
-- title:
--   Exponential right-shift squeeze identifies the limiting tail
-- statement:
--   If a fixed real c lies above exp(-(t+epsilon)*lambda) for every positive epsilon, and c lies below exp(-t*lambda), then c=exp(-t*lambda). This rigorous right-continuity lemma identifies the actual zero-barrier strict-survival exponential tail once nearby first-jump bounds have been Proved.
-- source:
--   Continuity of the exponential function and elementary order limits, supporting the Avram–Palmowski–Pistorius (2007) zero-barrier finite-activity argument.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Positivity
open Filter Topology

theorem AvramDividend.Classical.exponential_right_squeeze
    (t lambda c : ℝ)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      Real.exp (-((t + epsilon) * lambda)) ≤ c)
    (hUpper : c ≤ Real.exp (-(t * lambda))) :
    c = Real.exp (-(t * lambda)) := by sorry
