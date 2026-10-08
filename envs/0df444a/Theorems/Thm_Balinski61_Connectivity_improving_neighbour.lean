-- Prove2me | Theorems.Thm_Balinski61_Connectivity_improving_neighbour
-- name    : Balinski61.Connectivity.improving_neighbour
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:50:45.46187+00:00
-- url     : https://prove2.me/theorems/8a4e6ae7-87d2-45ef-a33d-1ccc52af7a67
-- title:
--   p. 432, proof of the THEOREM, case (a) — a non-maximal vertex has an improving neighbouring vertex
-- statement:
--   Let $S=\{x\in\mathbb R^n:\langle a_i,x\rangle\le b_i,\ i=1,\dots,m\}$ satisfy Balinski's standing assumptions: the only solution to $AX\le0$ is $X=0$, and some $X^0$ satisfies $AX^0<b$. Let $c\in\mathbb R^n$ and let $v$ be a vertex of $S$ at which the linear function $x\mapsto\langle c,x\rangle$ is not maximal on $S$, i.e. some $x\in S$ has $\langle c,x\rangle>\langle c,v\rangle$. Then there is a vertex $w$ of $S$, joined to $v$ by an edge of $S$, with
--   $$\langle c,w\rangle>\langle c,v\rangle .$$
--
--   This is the local-to-global principle of the simplex method, which Balinski's proof uses to climb from any vertex to the face where the function is maximal (or minimal) without leaving one side of a hyperplane.
--
--   **Formalization Note** The paper applies this to an affine function $y_0(x)=\langle c,x\rangle-d$; the constant $d$ cancels, so the linear form is stated. The paper's "(minimum)" alternative is the same statement for $-c$ and is not stated separately.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 432, proof of the THEOREM, case (a)

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

theorem improving_neighbour (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b) (c : EuclideanSpace ℝ (Fin n))
    (v : Set.extremePoints ℝ (Hirsch.Hpoly a b))
    (hv : ∃ x ∈ Hirsch.Hpoly a b, ⟪c, (v : EuclideanSpace ℝ (Fin n))⟫ < ⟪c, x⟫) :
    ∃ w : Set.extremePoints ℝ (Hirsch.Hpoly a b),
      (polyGraph (Hirsch.Hpoly a b)).Adj v w ∧
        ⟪c, (v : EuclideanSpace ℝ (Fin n))⟫ < ⟪c, (w : EuclideanSpace ℝ (Fin n))⟫ := by sorry

end Balinski61.Connectivity
