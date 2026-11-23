-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_Supplement_theorem_4_9
-- name    : BilevelSOC.SecondOrder.Supplement.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:46:26.022822+00:00
-- url     : https://prove2.me/theorems/5891730a-c4b8-4ce6-aab7-a534ab902f29
-- title:
--   Theorem 4.9 — Locally unique Lipschitz directional solution-map criterion
-- statement:
--   Let $D=(F,f,G,g)$ satisfy the standing $C^2$ assumptions and let $z=(\bar x,\bar y)$ be bilevel feasible. Suppose a neighborhood $U$ of $\bar x$ carries a locally Lipschitz, directionally differentiable function $s$ such that the entire solution set satisfies $S(x)=\{s(x)\}$ for every $x\in U$. Write $s'(\bar x;\delta_x)$ for its one-sided directional derivative. If
--
--   $$DF(z)(\delta_x,s'(\bar x;\delta_x))\le0,\quad DG_i(z)(\delta_x,s'(\bar x;\delta_x))\le0\quad(i\in\bar I^G)\quad\Longrightarrow\quad\delta_x=0,$$
--
--   then $z$ is a strict local minimizer of the bilevel program. This companion result uses the full locally singleton solution map, allowing nonlinear directional derivatives and imposing no Fréchet differentiability, convexity or LICQ.
--
--   Differences from the source:
--   - encoding: Euclidean coordinates and gradients, indexed from 1 → published E and Y spaces, uncurried pairs, Fin indices from 0, and Fréchet derivatives or partial Euclidean gradients; reason: the same finite-dimensional data; derivative evaluation equals the gradient pairing under Standing D
--   - encoding: s:U→ℝᵐ on a neighborhood of x̄, locally Lipschitz and directionally differentiable → a total extension s, open U containing x̄, all local regularity on U, and named directional values s′ at x̄; reason: one may shrink to an open neighborhood and extend arbitrarily outside U; every limit is local to U and S(x)={s(x)} on all of U
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 13, Theorem 4.9

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_FirstOrder
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
theorem theorem_4_9 {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (U : Set (E n)) (s : E n → Y m) (s' : E n → Y m)
    (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hU : IsOpen U) (hxU : z.1 ∈ U)
    (hs : ∀ x ∈ U, solMap D x = {s x})
    (hLip : ∀ x ∈ U, LocallyLipschitzAt s x)
    (hDir : ∀ x ∈ U, ∀ d, ∃ v, HasVectorDirDerivAt s x d v)
    (hs' : ∀ d, HasVectorDirDerivAt s z.1 d (s' d))
    (hexclude : ∀ dx, fderiv ℝ D.F z (dx, s' dx) ≤ 0 →
      (∀ i ∈ actG D z, fderiv ℝ (D.G i) z (dx, s' dx) ≤ 0) → dx = 0) :
    StrictLocalMin D.F (feasSet D) z := by sorry
end BilevelSOC.SecondOrder.Supplement
