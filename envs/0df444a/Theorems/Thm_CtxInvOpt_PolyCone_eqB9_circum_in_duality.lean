-- Prove2me | Theorems.Thm_CtxInvOpt_PolyCone_eqB9_circum_in_duality
-- name    : CtxInvOpt.PolyCone.eqB9_circum_in_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:57.305662+00:00
-- url     : https://prove2.me/theorems/b5882baf-5c5a-4156-9e04-73e676d0b26a
-- title:
--   (B-9), App-20 — µ²(K) + ρ²(K⋆) = 1 (Henrion–Seeger) for every closed convex pointed cone K ≠ {0}
-- statement:
--   Let $K\subseteq\mathbb R^p$ be a closed convex cone which is pointed ($K\cap(-K)=\{0\}$) and is not $\{0\}$, and let $K^\star=\{c\in\mathbb R^p:\ c'x\ge0\ \forall x\in K\}$ be its dual cone. With the circumradius $\mu(K)=\sin\alpha(K)$, where $\alpha$ is the uncertainty angle (9), and the inradius $\rho(K^\star)=\max_{x\in S^p\cap K^\star}\min_{y\in\partial K^\star}\|x-y\|$,
--   $$\mu^2(K)+\rho^2(K^\star)=1. \tag{B-9}$$
--
--   The circumradius measures the narrowest revolution cone containing $K$, the inradius the widest revolution cone inside $K^\star$; the identity says that the two problems are dual. In the proof of Lemma 10 it is applied to $K=K_{t+1}$, the dual of a simplicial cone, and turns the lower bound on an inradius (Lemmas B-2 to B-4) into the upper bound (B-8) on an uncertainty angle.
--
--   **Formalization Note** The page states (B-9) for every closed convex cone, citing Henrion and Seeger (2010, Theorem 1.4), with $\mu(K)=\sin\alpha(K)$ defined on App-19 for convex, closed and pointed cones; the statement is posed on exactly that class. The cone $\{0\}$ is excluded: its dual is $\mathbb R^p$, which has empty boundary, and the Lean distance to the empty set is the junk value $0$. Pointedness, closedness, convexity and the cone property are explicit hypotheses. The dual cone is the platform definition `ConvexOptimization.dualCone`.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. App-20, proof of Lemma 10, (B-9) (Henrion and Seeger, 2010, Theorem 1.4)

import Mathlib
import Definitions.Def_CtxInvOpt_PolyCone_Cones
import Definitions.Def_dualCone

namespace CtxInvOpt.PolyCone

/-- **(B-9), arXiv:2106.14015v3, App-20 (Henrion and Seeger, 2010, Theorem 1.4).**
Let `K ⊆ ℝ^p` be a closed convex pointed cone (the class on which App-19 defines `µ(K) = sin α(K)`),
other than `{0}`. Then `µ²(K) + ρ²(K⋆) = 1`, where `µ = sin α` is the circumradius, `ρ` the inradius
and `K⋆ = {c : c′x ≥ 0 ∀ x ∈ K}` the dual cone of `K`. -/
theorem eqB9_circum_in_duality {p : ℕ} (K : Set (EuclideanSpace ℝ (Fin p)))
    (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (hcone : ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K)
    (hpointed : ∀ x ∈ K, -x ∈ K → x = 0) (hne : ∃ x ∈ K, x ≠ 0) :
    circumradius K ^ 2 + inradius (ConvexOptimization.dualCone K) ^ 2 = 1 := by sorry

end CtxInvOpt.PolyCone
