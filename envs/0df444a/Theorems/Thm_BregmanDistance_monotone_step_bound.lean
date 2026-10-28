-- Prove2me | Theorems.Thm_BregmanDistance_monotone_step_bound
-- name    : BregmanDistance.monotone_step_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T14:35:51.176354+00:00
-- url     : https://prove2.me/theorems/1d53a2f9-dbfe-4db3-9c1f-ef9b56621e08
-- title:
--   One Bregman proximal step against a monotone operator: $c\langle w,p-v\rangle\le D(v,y)-D(v,p)-D(p,y)$
-- statement:
--   Let $T : H \rightrightarrows H$ be a monotone operator, let $h : H \to \mathbb{R}$, let $c > 0$, and suppose
--
--   $$
--   c^{-1}\big(\nabla h(y) - \nabla h(p)\big) \;\in\; T(p),
--   $$
--
--   which says that $p$ is the point produced by **one Bregman proximal step** of size $c$ from $y$, in the form $p = (\nabla h + cT)^{-1}(\nabla h(y))$. Then for every $v \in H$ and every $w \in T(v)$,
--
--   $$
--   c\,\big\langle w,\, p-v \big\rangle \;\le\; D(v,y) - D(v,p) - D(p,y).
--   $$
--
--   This is the engine of the whole convergence analysis. The left-hand side is where the data of the problem enters — a point $(v,w)$ of the graph of $T$ — while the right-hand side is a difference of $D$-values along the step. Two specializations do most of the work: taking $(v,w) = (z,0)$ for a zero $z$ of $T$ gives Fej\'er monotonicity of the iterates in the $D$-function together with summability of the consecutive terms $D(p^{k+1},p^k)$; keeping $(v,w)$ a general graph point instead gives the inequality that identifies every limit point of the sequence as a zero, via maximality of $T$.
--
--   Only monotonicity of $T$ is used, and nothing is assumed about $h$ beyond having a gradient, so the statement separates cleanly from the Bregman-function axioms, which enter afterwards through nonnegativity and the level-set bounds.
--
--   **Formalization Note** The proof applies monotonicity of $T$ at the pair $(p, v)$, scales the resulting inequality by $c > 0$, and rewrites the right-hand side with the three-point identity.
-- source:
--   The inequality driving the proof of Theorem 1 in Eckstein, Nonlinear Proximal Point Algorithms Using Bregman Functions, with Applications to Convex Programming, Math. Oper. Res. 18(1) (1993) 202-226, DOI 10.1287/moor.18.1.202, pp. 206-209; stated here for a single step and an arbitrary point of the graph of $T$.

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open BregmanPPA.Convergence ThreeOpSplitting.Convergence Filter Topology

namespace BregmanDistance

/-- Monotonicity of `T` turns one Bregman proximal step into a three-point inequality. -/
theorem monotone_step_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (T : H → Set H) (h : H → ℝ)
    (hT : IsMonotoneOp T) (v w y p : H) (c : ℝ) (hc : 0 < c) (hw : w ∈ T v)
    (hp : c⁻¹ • (gradient h y - gradient h p) ∈ T p) :
    c * inner ℝ w (p - v) ≤ bregmanD h v y - bregmanD h v p - bregmanD h p y := by sorry

end BregmanDistance
