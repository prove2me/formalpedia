-- Prove2me | Theorems.Thm_ExecCompLP_LAD_minimal_values_eq
-- name    : ExecCompLP.LAD.minimal_values_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:23:37.282404+00:00
-- url     : https://prove2.me/theorems/c512164f-54ca-43e9-a30c-2e5f096a6f07
-- title:
--   §6, p. 143 — the two problems have equal minimal values
-- statement:
--   Let $F$ be the feasible weight vectors specified by (2), and let $G$ be the feasible triples $(a,u,v)$ specified by (2), (4), and (5). For every real threshold $t$,
--
--   $$\bigl(\exists a\in F:\ D(a)\le t\bigr)\quad\Longleftrightarrow\quad\bigl(\exists(a,u,v)\in G:\ P(u,v)\le t\bigr),$$
--
--   where $D(a)=\sum_{k\in K}|S_k(a)-s_k|$ and $P(u,v)=\sum_{k\in K}(u_k+v_k)$. Consequently the two problems have the same attainable objective thresholds and, whenever a minimum is attained, the same minimum value.
--
--   **Formalization Note** Threshold equivalence also covers an empty feasible set without assigning a default real value to its infimum.
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), p. 143, §6, first full paragraph; https://doi.org/10.1287/mnsc.1.2.138

import Mathlib
import Definitions.Def_ExecCompLP_LAD_Setting

namespace ExecCompLP.LAD

theorem minimal_values_eq {n L : ℕ} [NeZero L]
    (x : Fin n → Fin L → ℝ) (sM sm : ℝ) (K : Finset (Fin L))
    (s : Fin L → ℝ) :
    ∀ t : ℝ,
      (∃ a : Fin n → ℝ, Feasible x sM sm a ∧ obj x K s a ≤ t) ↔
      (∃ (a : Fin n → ℝ) (u v : Fin L → ℝ),
        LPFeasible x sM sm K s a u v ∧ lpObj K u v ≤ t) := by sorry

end ExecCompLP.LAD
