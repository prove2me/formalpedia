-- Prove2me | Theorems.Thm_BregmanDistance_step_fejer_monotone
-- name    : BregmanDistance.step_fejer_monotone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T14:35:43.016082+00:00
-- url     : https://prove2.me/theorems/0e9c4d45-cafd-4f14-af54-74660fda0a9f
-- title:
--   A Bregman proximal step is Fej\'er monotone: $D(z,p)\le D(z,y)-D(p,y)$ for every zero $z$
-- statement:
--   Let $T : H \rightrightarrows H$ be monotone, let $c > 0$, and let $p$ be produced by one Bregman proximal step of size $c$ from $y$, i.e.
--
--   $$
--   c^{-1}\big(\nabla h(y) - \nabla h(p)\big) \;\in\; T(p).
--   $$
--
--   Then for every zero $z$ of $T$ (that is, $0 \in T(z)$),
--
--   $$
--   D(z,p) \;\le\; D(z,y) \;-\; D(p,y).
--   $$
--
--   Two conclusions follow at once, and they are the two halves of every proof of convergence for a Bregman proximal point method. First, since $D(p,y) \ge 0$, the sequence $k \mapsto D(z, p^k)$ is **nonincreasing** along a run of the algorithm: the iterates are Fej\'er monotone with respect to the zero set, measured in the $D$-function rather than in the norm. Second, summing the inequality over $k$ shows that
--
--   $$
--   \sum_{k} D(p^{k+1}, p^{k}) \;\le\; D(z, p^{0}) \;<\; \infty,
--   $$
--
--   so consecutive iterates come together in the $D$-function. Combined with the boundedness of $D$-level sets that Definition 1 demands, the first gives boundedness of the run and the second gives that every limit point is a zero.
--
--   The step size $c$ has disappeared from the conclusion: it only had to be positive.
--
--   **Formalization Note** This is the previous inequality at the graph point $(v,w) = (z,0)$, where the left-hand side $c\langle 0, p-z\rangle$ vanishes.
-- source:
--   The Fejér-monotonicity step in the proof of Theorem 1 of Eckstein, Nonlinear Proximal Point Algorithms Using Bregman Functions, with Applications to Convex Programming, Math. Oper. Res. 18(1) (1993) 202-226, DOI 10.1287/moor.18.1.202, pp. 206-209 (Step 1).

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open BregmanPPA.Convergence ThreeOpSplitting.Convergence Filter Topology

namespace BregmanDistance

/-- A Bregman proximal step is Fejér monotone in the D-function with respect to any zero. -/
theorem step_fejer_monotone {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (T : H → Set H) (h : H → ℝ)
    (hT : IsMonotoneOp T) (z y p : H) (c : ℝ) (hc : 0 < c) (hz : z ∈ zer T)
    (hp : c⁻¹ • (gradient h y - gradient h p) ∈ T p) :
    bregmanD h z p ≤ bregmanD h z y - bregmanD h p y := by sorry

end BregmanDistance
