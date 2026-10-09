-- Prove2me | Theorems.Thm_DIGing_Push_rt_row_stochastic
-- name    : DIGing.Push.rt_row_stochastic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:39.48409+00:00
-- url     : https://prove2.me/theorems/48f03cde-e894-4da6-978b-71645cfaa765
-- title:
--   §5, p. 22 — R̃(k) = V(k+1)⁻¹C(k)V(k) is a row stochastic matrix
-- statement:
--   Let the mixing matrices $C(k)$ satisfy Assumption 7, let $\mathbf v(0)=\mathbf 1$, $\mathbf v(k+1)=C(k)\mathbf v(k)$, $V(k)=\operatorname{diag}\{\mathbf v(k)\}$, and $\tilde R(k)=V(k+1)^{-1}C(k)V(k)$. Then for every $k$, $\tilde R(k)$ is row stochastic: for all $i,j$
--   $$\tilde R_{ij}(k)\ge0\qquad\text{and}\qquad \sum_{j=1}^n\tilde R_{ij}(k)=1.$$
--
--   Row stochasticity of $\tilde R(k)$ is what lets the recursion (48) be analysed like DIGing: multiplication by $\tilde R(k)$ maps consensual matrices to themselves.
--
--   **Formalization Note** The paper cites Lemma 4 of [41] and says "every row sums to 1"; the nonnegativity of the entries, which is part of "row stochastic", is included. Assumption 7 includes the disclosed self-weight; Assumption 6 is not needed.
-- source:
--   arXiv:1607.03218v3, §5, p. 22 (sentence after (49)); proof of Lemma 13, p. 23

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Push_Setting

namespace DIGing.Push

theorem rt_row_stochastic {n : ℕ} (A : ℕ → Finset (Fin n × Fin n))
    (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (h7 : Assumption7 A C) :
    ∀ k i, (∀ j, 0 ≤ Rt C k i j) ∧ ∑ j, Rt C k i j = 1 := by sorry

end DIGing.Push
