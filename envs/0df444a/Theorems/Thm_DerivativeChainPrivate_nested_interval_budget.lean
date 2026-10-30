-- Prove2me | Theorems.Thm_DerivativeChainPrivate_nested_interval_budget
-- name    : DerivativeChainPrivate.nested_interval_budget
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:13:45.800342+00:00
-- url     : https://prove2.me/theorems/1b336346-cbe9-444f-9f14-545919c22c39
-- title:
--   Scalar budget for nested real intervals
-- statement:
--   For 0 <= a <= A, 0 <= b <= B and A+B > 0, the inequality 2(AB-ab)/(A+B) <= 2(sqrt(AB)-sqrt(ab)) holds. The old interval may be a singleton. This scalar inequality does not construct a martingale, select derivative roots, or prove an unrestricted chain bound.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/52c50aeb6d4adf24f4ae03d555d1181eae370084/results/verified-supporting-lemmas-20261017/interval/Solution.lean#L9-L30

import Mathlib
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate Filter Topology Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem DerivativeChainPrivate.nested_interval_budget (a b A B : ℝ)
    (ha : 0 ≤ a) (haA : a ≤ A) (hb : 0 ≤ b) (hbB : b ≤ B)
    (hAB : 0 < A + B) :
    2 * (A * B - a * b) / (A + B) ≤
      2 * (Real.sqrt (A * B) - Real.sqrt (a * b)) := by sorry
