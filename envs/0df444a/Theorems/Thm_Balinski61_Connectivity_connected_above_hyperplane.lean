-- Prove2me | Theorems.Thm_Balinski61_Connectivity_connected_above_hyperplane
-- name    : Balinski61.Connectivity.connected_above_hyperplane
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:50:39.034927+00:00
-- url     : https://prove2.me/theorems/cfc3be66-2ff7-4419-961f-b7c6765c5ade
-- title:
--   p. 433, proof of the THEOREM, case (a) — vertices strictly above a hyperplane are joined by a path staying above it
-- statement:
--   Let $S=\{x\in\mathbb R^n:\langle a_i,x\rangle\le b_i,\ i=1,\dots,m\}$ satisfy Balinski's standing assumptions: the only solution to $AX\le0$ is $X=0$, and some $X^0$ satisfies $AX^0<b$. Let $G(S)$ be the graph of its vertices and edges. Let $c\in\mathbb R^n$, $d\in\mathbb R$, and let $u,v$ be vertices of $S$ with
--   $$\langle c,u\rangle>d\quad\text{and}\quad\langle c,v\rangle>d .$$
--   Then there is a path $u=w_0,w_1,\dots,w_k=v$ in $G(S)$ all of whose points satisfy $\langle c,w_j\rangle>d$.
--
--   In the paper $y_0(x)=\langle c,x\rangle-d$ is the affine function whose zero set is a hyperplane through the deleted vertices $v_1,\dots,v_{n-1}$ and one further vertex $v_0$; case (a) concludes "there exists a path $v_p\leftrightarrow v_q$ all of whose points $v$ satisfy $y_0(v)>0$". Since the deleted vertices lie on the hyperplane, such a path avoids them. The proof of the THEOREM uses this conclusion in cases (a), (b) and (c).
--
--   **Formalization Note** The statement is given for an arbitrary affine function, not only the particular $y_0$ of the proof, and only in the "$>$" form; the "$<$" form is the same statement for $-c,-d$. A path of the paper is a Mathlib `Walk` in `polyGraph S` (consecutive points are adjacent, hence distinct); the condition is imposed on every point of its support.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), pp. 432–433, proof of the THEOREM, case (a), concluding sentence on p. 433

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

theorem connected_above_hyperplane (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b) (c : EuclideanSpace ℝ (Fin n)) (d : ℝ)
    (u v : Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hu : d < ⟪c, (u : EuclideanSpace ℝ (Fin n))⟫)
    (hv : d < ⟪c, (v : EuclideanSpace ℝ (Fin n))⟫) :
    ∃ p : (polyGraph (Hirsch.Hpoly a b)).Walk u v,
      ∀ x ∈ p.support, d < ⟪c, (x : EuclideanSpace ℝ (Fin n))⟫ := by sorry

end Balinski61.Connectivity
