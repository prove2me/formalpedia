-- Prove2me | Theorems.Thm_ConsistentSubmodular_exp_neg_le_quadratic
-- name    : ConsistentSubmodular.exp_neg_le_quadratic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:53.720831+00:00
-- url     : https://prove2.me/theorems/d21bf8fd-620d-4db7-82f8-830b0c9900d4
-- title:
--   Quadratic upper bound on $e^{-x}$ for $x\ge 0$
-- statement:
--   For every real number $x\ge 0$,
--
--   $$e^{-x}\;\le\;1-x+\frac{x^2}{2}.$$
--
--   This elementary scalar inequality is one ingredient of the exponential-moment estimates used for the concentration bounds (lower tail of a submodular function and Chernoff-type bounds) in the rounding of fractional windows.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ExponentialTails.lean#L33-L49 (`ConsistentSubmodular.exp_neg_le_quadratic`)

import Mathlib

open scoped BigOperators

theorem ConsistentSubmodular.exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by sorry
