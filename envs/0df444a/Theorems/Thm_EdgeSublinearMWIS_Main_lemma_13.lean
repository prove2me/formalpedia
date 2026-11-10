-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_lemma_13
-- name    : EdgeSublinearMWIS.Main.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:42:02.683207+00:00
-- url     : https://prove2.me/theorems/f8f9e22e-f403-4e1d-8e32-77e7faf20e6f
-- title:
--   Lemma 13 — valid component inequalities and strict violation
-- statement:
--   Let $G$ be finite, $r\ge1$ and $k$ an integer target. Let $D\subseteq V(G)$, $u\ge\alpha(G[D])$, and $A\subseteq V(G)$ with $|A|\le r$. Every point $z$ of the true indicator convex hull $P_r(G,k)$ satisfies
--   $$\sum_{v\in D}z_{A\cup\{v\}}\le uz_A.$$
--   In addition, every real query $y$ with $y_A>0$ and $\sum_{v\in D}y_{A\cup\{v\}}/y_A>u$ strictly violates this inequality. Neither membership of $y$ in the hull nor exactness of $u$ is assumed. Both clauses are included in the same item. They turn an induced-subgraph upper bound into a valid cut for a fixed polytope.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: finite coordinate vectors → total arrays restricted by InHull to the true coordinates; reason: out-of-range entries cannot enter either clause
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Lemma 13, p.15 (PDF p.15), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Relaxation

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

/-- Validity on the true indicator hull, and strict violation by arbitrary real y. -/
theorem lemma_13 {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (k : ℤ) (hr : 1 ≤ r)
    (D A : Finset (Fin n)) (u : ℝ) (upper : (alpha G D : ℝ) ≤ u) (size : A.card ≤ r) :
    (∀ z : Finset (Fin n) → ℝ, InHull G Finset.univ r k z →
      (∑ v ∈ D, z (insert v A)) ≤ u * z A) ∧
    (∀ y : Finset (Fin n) → ℝ, 0 < y A →
      u < (∑ v ∈ D, y (insert v A) / y A) →
      u * y A < ∑ v ∈ D, y (insert v A)) := by sorry

end EdgeSublinearMWIS.Main
