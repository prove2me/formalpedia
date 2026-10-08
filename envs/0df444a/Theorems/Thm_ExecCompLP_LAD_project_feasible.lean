-- Prove2me | Theorems.Thm_ExecCompLP_LAD_project_feasible
-- name    : ExecCompLP.LAD.project_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:23:20.248453+00:00
-- url     : https://prove2.me/theorems/75671ec3-5eda-4e62-9ea3-1d119d1e1ca3
-- title:
--   §6, p. 143 — projection of a split-variable feasible point
-- statement:
--   Let $(a,u,v)$ satisfy the ranked salary constraints (2) and the transformed constraints $u_k,v_k\ge 0$ and $S_k(a)-s_k=u_k-v_k$ for each $k\in K$. The projected weight vector $a$ is feasible for the original problem, and
--
--   $$\sum_{k\in K}|S_k(a)-s_k|\le\sum_{k\in K}(u_k+v_k).$$
--
--   Thus every point of the transformed problem has an associated point of the original problem whose objective is no larger.
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), p. 143, §6, first full paragraph; https://doi.org/10.1287/mnsc.1.2.138

import Mathlib
import Definitions.Def_ExecCompLP_LAD_Setting

namespace ExecCompLP.LAD

theorem project_feasible {n L : ℕ} [NeZero L]
    (x : Fin n → Fin L → ℝ) (sM sm : ℝ) (K : Finset (Fin L))
    (s : Fin L → ℝ) (a : Fin n → ℝ) (u v : Fin L → ℝ)
    (h : LPFeasible x sM sm K s a u v) :
    Feasible x sM sm a ∧ obj x K s a ≤ lpObj K u v := by sorry

end ExecCompLP.LAD
