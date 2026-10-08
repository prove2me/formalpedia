-- Prove2me | Theorems.Thm_ExecCompLP_Consistency_value_lipschitz
-- name    : ExecCompLP.Consistency.value_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:25:46.772981+00:00
-- url     : https://prove2.me/theorems/f4d729c9-bda4-4e7b-a56d-80b9b719eafb
-- title:
--   §8, Proof, p. 151 — there is B > 0 with |c′(α − a)| ≤ B|α − a| for all α, a
-- statement:
--   Let $c\in\mathbb R^n$. There exists a constant $B>0$ such that for all $\alpha,a\in\mathbb R^n$,
--
--   $$\Bigl|\sum_j c_j(\alpha_j-a_j)\Bigr|\le B\,|\alpha-a|.$$
--
--   This is the displayed step on p. 151: since $\sum_j c_ja_j$ is a linear functional, the difference of its values at two points is at most $B$ times the distance between them. In the proof it bounds how much the objective can change between an extreme point of the true set and the corresponding extreme point of the sample set.
--
--   **Formalization Note** $|\alpha-a|$ is the maximum norm $\max_j|\alpha_j-a_j|$; the paper names no norm and the statement is the same for every norm on $\mathbb R^n$ (with a different $B$).
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), p. 151, §8, Proof, display |c′(α − a)| ≦ B|α − a|

import Mathlib
import Definitions.Def_ExecCompLP_Consistency_Setting

namespace ExecCompLP.Consistency

theorem value_lipschitz {n : ℕ} (c : Fin n → ℝ) :
    ∃ B > 0, ∀ α a : Fin n → ℝ, |∑ j, c j * (α j - a j)| ≤ B * ‖α - a‖ := by sorry

end ExecCompLP.Consistency
