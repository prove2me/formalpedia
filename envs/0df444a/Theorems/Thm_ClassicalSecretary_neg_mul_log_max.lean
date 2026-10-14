-- Prove2me | Theorems.Thm_ClassicalSecretary_neg_mul_log_max
-- name    : ClassicalSecretary.neg_mul_log_max
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T12:53:28.022521+00:00
-- url     : https://prove2.me/theorems/c85154fa-3915-494f-818e-3f691dd0cba8
-- title:
--   $-x\log x$ is maximized on $[0,1]$ exactly at $x=1/e$, with value $1/e$
-- statement:
--   Let $P(x) = -x\log x$ on $[0,1]$, with $P(0)=0$. Then:
--   1. $P(x) \le 1/e$ for every $x \in [0,1]$;
--   2. $P(1/e) = 1/e$;
--   3. if $P(x) = 1/e$ for some $x\in[0,1]$, then $x = 1/e$.
--
--   This identifies the limiting optimal cutoff fraction and the limiting optimal success probability.
-- source:
--   Wikipedia, "Secretary problem", https://en.wikipedia.org/wiki/Secretary_problem, section "Deriving the optimal policy": "Taking the derivative of P(x) with respect to x, setting it to 0, and solving for x, we find that the optimal x is equal to 1/e".

import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem neg_mul_log_max :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, -x * Real.log x ≤ Real.exp (-1)) ∧
    -Real.exp (-1) * Real.log (Real.exp (-1)) = Real.exp (-1) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, -x * Real.log x = Real.exp (-1) → x = Real.exp (-1)) := by sorry

end ClassicalSecretary
