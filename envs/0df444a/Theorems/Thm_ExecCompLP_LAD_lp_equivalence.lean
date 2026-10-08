-- Prove2me | Theorems.Thm_ExecCompLP_LAD_lp_equivalence
-- name    : ExecCompLP.LAD.lp_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:23:26.672495+00:00
-- url     : https://prove2.me/theorems/26ca4899-6ac1-413d-9a31-b2821639f29d
-- title:
--   §§5–6, pp. 141–143 — ranked least absolute deviations equal a linear program
-- statement:
--   For arbitrary real factor ratings $x_{ik}$, nonnegative-weight salary constraints (2), specified levels $K$, and targets $s_k$, compare minimizing $D(a)=\sum_{k\in K}|S_k(a)-s_k|$ with the transformed linear program minimizing $P(u,v)=\sum_{k\in K}(u_k+v_k)$ subject to (2), $u_k,v_k\ge0$, and $S_k(a)-s_k=u_k-v_k$ for $k\in K$. The two problems have the same attainable objective thresholds:
--
--   $$\forall t\in\mathbb R,\quad [\exists a\text{ feasible}:D(a)\le t]\ \Longleftrightarrow\ [\exists(a,u,v)\text{ LP-feasible}:P(u,v)\le t].$$
--
--   Moreover, $a$ minimizes $D$ if and only if $(a,w^+,w^-)$ minimizes $P$, where $w_k=S_k(a)-s_k$; and every LP minimizer $(a,u,v)$ projects to a minimizer $a$ of $D$.
--
--   This states both the agreement of optimal values and the correspondence of optimal solutions claimed in §§5–6.
--
--   **Formalization Note** There is at least one ranked level. No existence of a feasible point or minimizer is assumed; the threshold statement retains meaning when the constraints are infeasible. The LP's split variables are free subject to (4)–(5), including feasible pairs with both entries positive.
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), pp. 141–143, §§5–6, equations (2)–(5) and equivalence claim on p. 143; https://doi.org/10.1287/mnsc.1.2.138

import Mathlib
import Definitions.Def_ExecCompLP_LAD_Setting

namespace ExecCompLP.LAD

theorem lp_equivalence {n L : ℕ} [NeZero L]
    (x : Fin n → Fin L → ℝ) (sM sm : ℝ) (K : Finset (Fin L))
    (s : Fin L → ℝ) :
    (∀ t : ℝ,
      (∃ a : Fin n → ℝ, Feasible x sM sm a ∧ obj x K s a ≤ t) ↔
      (∃ (a : Fin n → ℝ) (u v : Fin L → ℝ),
        LPFeasible x sM sm K s a u v ∧ lpObj K u v ≤ t)) ∧
    (∀ a : Fin n → ℝ,
      IsMinimizer x sM sm K s a ↔
      IsLPMinimizer x sM sm K s a
        (fun k => posPart (salary x a k - s k))
        (fun k => negPart (salary x a k - s k))) ∧
    (∀ (a : Fin n → ℝ) (u v : Fin L → ℝ),
      IsLPMinimizer x sM sm K s a u v → IsMinimizer x sM sm K s a) := by sorry

end ExecCompLP.LAD
