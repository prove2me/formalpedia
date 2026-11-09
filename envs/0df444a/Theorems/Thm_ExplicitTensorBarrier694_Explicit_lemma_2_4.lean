-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_lemma_2_4
-- name    : ExplicitTensorBarrier694.Explicit.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:00.280602+00:00
-- url     : https://prove2.me/theorems/12ef66ab-a260-4061-b1c6-7608dfb1a36e
-- title:
--   Lemma 2.4 — border substitution
-- statement:
--   Let $T\in(\mathbb C^n)^{\otimes3}$ have injective first contraction map, and let $1\le q\le n$. Then
--
--   $$\underline R(T)\ge n-q+\min_{W\in\operatorname{Gr}(q,(\mathbb C^n)^*)}\underline R(T|_W).$$
--
--   The minimum ranges over every complex $q$-dimensional dual subspace, not just coordinate subspaces. It is attained because the nonempty family of natural-number ranks has a least element. This is the border-substitution ingredient for Theorem 3.5; conciseness is a hypothesis here, to be established separately when using the explicit witness.
--
--   Differences from the source:
--   - encoding: arbitrary finite-dimensional complex mode spaces → coordinate spaces with arbitrary natural dimensions; reason: choosing bases identifies every source instance with one of these arrays; tensors, dual subspaces, and Koszul maps are transported by those bases
--   - encoding: least rank in a complex limit → least r whose rank-at-most-r locus has the tensor in its topological closure; reason: finite complex product spaces are metrizable, so sequential limits and closure agree; approximants remain arbitrary complex tensors
--   - encoding: Grassmannian minimum of restricted border ranks → Nat infimum of the same value set, restrictions in a chosen basis of each W; reason: q≤n ensures a nonempty Grassmannian; a nonempty set of natural numbers attains its infimum, and changing the basis of W preserves tensor and border rank
--   - encoding: integer-valued lower bound n−q+minimum → the same inequality after casting all ranks and dimensions to integers; reason: integer subtraction avoids truncation and preserves the exact inequality
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Lemma 2.4, p.7, equation (2.3) (PDF p.7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Tensors

namespace ExplicitTensorBarrier694.Explicit

/-- Lovitz, STOC 2027 submission #694 (October 2026), Lemma 2.4, p.7.
The infimum is the attained minimum over ALL q-dimensional dual subspaces.
Subtraction in the displayed lower bound is in ℤ, with no truncation. -/
theorem lemma_2_4 {n : ℕ} (T : Tensor n n n) (hT : AConcise T)
    (q : ℕ) (hq : 1 ≤ q) (hqn : q ≤ n) :
    (n : ℤ) - (q : ℤ) + (restrictionMinimum T q : ℤ) ≤ (borderRank T : ℤ) := by sorry

end ExplicitTensorBarrier694.Explicit
