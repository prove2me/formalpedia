-- Prove2me | Theorems.Thm_DiaconisStroock_OddPaths_two_mul_eq_alternating_sum
-- name    : DiaconisStroock.OddPaths.two_mul_eq_alternating_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:08.490095+00:00
-- url     : https://prove2.me/theorems/fed7cc2e-e325-4ff6-a5d1-dc02e79b5c35
-- title:
--   §1C, proof of Proposition 2, p. 40 — φ(x) = ½{(φ(x)+φ(y)) − (φ(y)+φ(w)) + ⋯ + (φ(z)+φ(x))} along an odd closed path
-- statement:
--   Let $x\in X$ and let $\sigma=[v_0,v_1,\dots,v_k]$ be a closed vertex sequence at $x$, i.e. $v_0=v_k=x$, with an odd number $k$ of steps. Write $e_i=(v_i,v_{i+1})$ for its $i$-th step, $i=0,\dots,k-1$, with initial point $e_i^-=v_i$ and end point $e_i^+=v_{i+1}$. Then for every function $\varphi:X\to\mathbb R$,
--
--   $$
--   2\varphi(x)=\sum_{i=0}^{k-1}(-1)^{i}\big(\varphi(e_i^-)+\varphi(e_i^+)\big)
--   =(\varphi(x)+\varphi(v_1))-(\varphi(v_1)+\varphi(v_2))+\dots+(\varphi(v_{k-1})+\varphi(x)).
--   $$
--
--   This is the representation on which the proof of Proposition 2 rests: an odd closed path writes $\varphi(x)$ as an alternating sum of the edge quantities $\varphi(e^-)+\varphi(e^+)$, to which Cauchy–Schwarz is then applied. The sign $(-1)^{i}$ is the paper's $(-1)^{l(e)}$, with $l(e)$ the distance of $e^-$ from $x$ along the path.
--
--   **Formalization Note** The page states $\varphi(x)=\tfrac12\{\dots\}$; the statement is written with $2\varphi(x)$ on the left, which is the same claim without a division. No Markov chain enters: the identity holds for any closed sequence with an odd number of steps, whether or not its steps are edges.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 40, §1C, proof of Proposition 2 (display after (1.8)), https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths

namespace DiaconisStroock.OddPaths

theorem two_mul_eq_alternating_sum {V : Type*} (x : V) (p : List V) (hhead : p.head? = some x)
    (hlast : p.getLast? = some x) (hodd : Odd (DiaconisStroock.Poincare.pathEdges p).length) :
    ∀ φ : V → ℝ,
      2 * φ x = ((DiaconisStroock.Poincare.pathEdges p).mapIdx fun i e => (-1 : ℝ) ^ i * (φ e.1 + φ e.2)).sum := by sorry

end DiaconisStroock.OddPaths
