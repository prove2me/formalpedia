-- Prove2me | Theorems.Thm_BregmanDistance_three_point_identity
-- name    : BregmanDistance.three_point_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T14:35:44.562983+00:00
-- url     : https://prove2.me/theorems/88c5b5e1-634b-4fbb-8dca-6174a2fb2734
-- title:
--   Three-point identity: $D(v,y)-D(v,p)-D(p,y)=\langle p-v,\nabla h(y)-\nabla h(p)\rangle$
-- statement:
--   Let $H$ be a finite-dimensional real inner product space and let $h : H \to \mathbb{R}$. Its **$D$-function** (Bregman distance) is
--
--   $$
--   D(x,y) \;=\; h(x) - h(y) - \langle \nabla h(y),\, x-y\rangle .
--   $$
--
--   Then for all $v, y, p \in H$,
--
--   $$
--   D(v,y) \;-\; D(v,p) \;-\; D(p,y) \;=\; \big\langle\, p-v,\; \nabla h(y)-\nabla h(p) \,\big\rangle .
--   $$
--
--   This is the **three-point identity**: it relates the three $D$-values formed by a reference point $v$, a current point $y$ and a successor point $p$ to a single inner product in which the two gradients appear. It is the algebraic core of every convergence proof for a Bregman proximal method. In such a method the successor $p$ satisfies $c^{-1}(\nabla h(y) - \nabla h(p)) \in T(p)$ for an operator $T$, so the right-hand side is exactly where monotonicity of $T$ can be applied; the left-hand side is then a telescoping combination of $D$-values. Taking $h = \tfrac12\|\cdot\|^2$, so that $D(x,y) = \tfrac12\|x-y\|^2$, recovers the familiar identity $\tfrac12\|v-y\|^2 - \tfrac12\|v-p\|^2 - \tfrac12\|p-y\|^2 = \langle p-v, y-p\rangle$.
--
--   **Formalization Note** No hypothesis is placed on $h$: the identity is pure algebra in the five scalars $h(v), h(y), h(p)$ and the inner products of $\nabla h(y), \nabla h(p)$ against the differences, so it holds for the platform's `bregmanD` whatever `gradient h` evaluates to. In particular it needs neither convexity of $h$ nor a zone, which is why it can be stated once and reused by every Bregman algorithm on the platform.
-- source:
--   The three-point identity used throughout the convergence analysis of Eckstein, Nonlinear Proximal Point Algorithms Using Bregman Functions, with Applications to Convex Programming, Math. Oper. Res. 18(1) (1993) 202-226, DOI 10.1287/moor.18.1.202, proof of Theorem 1, pp. 206-209 (the step preceding inequality (6)); stated here for an arbitrary differentiable $h$ with no zone or convexity hypothesis.

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open BregmanPPA.Convergence ThreeOpSplitting.Convergence Filter Topology

namespace BregmanDistance

/-- The three-point identity for the D-function of a differentiable `h`. -/
theorem three_point_identity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (h : H → ℝ) (v y p : H) :
    bregmanD h v y - bregmanD h v p - bregmanD h p y =
      inner ℝ (p - v) (gradient h y - gradient h p) := by sorry

end BregmanDistance
