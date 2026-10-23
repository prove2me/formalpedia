-- Prove2me | Theorems.Thm_AggNash_Existence_lemma_5_4_starr
-- name    : AggNash.Existence.lemma_5_4_starr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:18.923135+00:00
-- url     : https://prove2.me/theorems/02dc3b63-349e-44e8-837c-8cc34528681e
-- title:
--   Lemma 5.4 (second bullet), p. 17 — Starr's bound: some yᵢ ∈ Sᵢ has ‖x − Σ yᵢ‖ ≤ √(min{q, n}) · max diam Sᵢ
-- statement:
--   Let $S_1,\dots,S_m$ be compact subsets of $\mathbb R^q$, let $D$ be a bound on their diameters ($\operatorname{diam}S_i\le D$ for every $i$), and let $x\in\operatorname{conv}\sum_{i=1}^mS_i$, where the sum is the Minkowski sum. Then there are points $y_i\in S_i$ such that
--
--   $$
--   \Big\|x-\sum_{i=1}^my_i\Big\|\le\sqrt{\min\{q,m\}}\;D .
--   $$
--
--   This is the quantitative form of the Shapley–Folkman lemma (Starr's bound). In the mission it controls how far the aggregate of a disaggregated profile can move from the aggregate of an equilibrium of the convexified game.
--
--   **Formalization Note** The paper takes $D$ to be the maximal diameter of the $S_i$; here $D$ is any upper bound on all the diameters. The conclusion is monotone in $D$, so the two forms are equivalent. The norm is the Euclidean norm of `EuclideanSpace ℝ (Fin q)`.
-- source:
--   Liu, Oudjane & Wan, Approximate Nash equilibria in large non-convex aggregative games, arXiv:2011.12604v3, p. 17, Lemma 5.4 (second bullet)

import Mathlib
open scoped Pointwise

namespace AggNash.Existence

/-- Lemma 5.4, second bullet (p. 17). For compact sets `S₁, …, S_m ⊂ ℝ^q` and
`x ∈ conv ∑ᵢ Sᵢ`, there are `yᵢ ∈ Sᵢ` with `‖x − ∑ᵢ yᵢ‖ ≤ √(min{q, m}) · D`, where `D` bounds
the diameter of every `Sᵢ` (for instance the maximal diameter). -/
theorem lemma_5_4_starr (q m : ℕ) (S : Fin m → Set (EuclideanSpace ℝ (Fin q)))
    (hS : ∀ i, IsCompact (S i)) (x : EuclideanSpace ℝ (Fin q))
    (hx : x ∈ convexHull ℝ (∑ i, S i)) (D : ℝ) (hD : ∀ i, Metric.diam (S i) ≤ D) :
    ∃ y : Fin m → EuclideanSpace ℝ (Fin q), (∀ i, y i ∈ S i) ∧
      ‖x - ∑ i, y i‖ ≤ Real.sqrt (min q m : ℕ) * D := by sorry

end AggNash.Existence
