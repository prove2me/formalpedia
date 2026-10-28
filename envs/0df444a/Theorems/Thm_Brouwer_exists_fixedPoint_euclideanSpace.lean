-- Prove2me | Theorems.Thm_Brouwer_exists_fixedPoint_euclideanSpace
-- name    : Brouwer.exists_fixedPoint_euclideanSpace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:30.413239+00:00
-- url     : https://prove2.me/theorems/3fb494b3-fefa-4ede-bbea-3162ecbd612a
-- title:
--   Brouwer’s fixed point theorem for a compact convex set in Euclidean space
-- statement:
--   **Brouwer's fixed point theorem for a compact convex set.** Let $K \subseteq \mathbb{R}^d$
--   be nonempty, compact and convex, and let $f$ be continuous on $K$ with $f(K) \subseteq K$. Then
--
--   $$
--   \exists\, x \in K \ \text{ such that } \ f(x) = x .
--   $$
--
--   The ball is replaced by an arbitrary compact convex set, with no regularity assumed of its
--   boundary. In this form the theorem is the standard existence tool in equilibrium and
--   variational-inequality arguments, where the set is a simplex, a polytope or a feasible region
--   rather than a ball.
--
--   **Formalization Note** $K$ lives in `EuclideanSpace ℝ (Fin d)`, the continuity hypothesis
--   is `ContinuousOn f K`, and invariance is `Set.MapsTo f K K`.
-- source:
--   J. Milnor, Analytic proofs of the “hairy ball theorem” and the Brouwer fixed point theorem, Amer. Math. Monthly 85 (1978), 521–524, §1–§3; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.exists_fixedPoint_euclideanSpace {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hKconv : Convex ℝ K)
    (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f K)
    (hfK : MapsTo f K K) : ∃ x ∈ K, f x = x := by sorry
