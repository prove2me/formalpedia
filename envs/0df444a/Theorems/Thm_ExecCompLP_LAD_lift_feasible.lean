-- Prove2me | Theorems.Thm_ExecCompLP_LAD_lift_feasible
-- name    : ExecCompLP.LAD.lift_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:23:19.846181+00:00
-- url     : https://prove2.me/theorems/4ca5ed27-2bbe-40ec-aaec-f51f6305d0d5
-- title:
--   §5, p. 141 — every feasible deviation has nonnegative split variables
-- statement:
--   Let $a$ satisfy the nonnegative-weight, ceiling, ranking, and floor constraints (2). For each specified level $k\in K$, set $w_k=S_k(a)-s_k$, $u_k=\max(w_k,0)$, and $v_k=\max(-w_k,0)$. Then $(a,u,v)$ satisfies the transformed constraints (4)–(5), and
--
--   $$\sum_{k\in K}(u_k+v_k)=\sum_{k\in K}|S_k(a)-s_k|.$$
--
--   This identifies an LP-feasible point with the same objective for every feasible choice of salary weights.
--
--   **Formalization Note** The split variables are functions on all ranked levels, but their signs and defining equations are required only at the specified levels $K$, as in the paper.
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), p. 141, §5, equations (4)–(5) and sentence following (5); https://doi.org/10.1287/mnsc.1.2.138

import Mathlib
import Definitions.Def_ExecCompLP_LAD_Setting

namespace ExecCompLP.LAD

theorem lift_feasible {n L : ℕ} [NeZero L]
    (x : Fin n → Fin L → ℝ) (sM sm : ℝ) (K : Finset (Fin L))
    (s : Fin L → ℝ) (a : Fin n → ℝ) (ha : Feasible x sM sm a) :
    LPFeasible x sM sm K s a
      (fun k => posPart (salary x a k - s k))
      (fun k => negPart (salary x a k - s k)) ∧
    lpObj K
      (fun k => posPart (salary x a k - s k))
      (fun k => negPart (salary x a k - s k)) = obj x K s a := by sorry

end ExecCompLP.LAD
