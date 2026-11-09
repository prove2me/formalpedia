-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_lemma_3_4
-- name    : ExplicitTensorBarrier694.Explicit.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:58.248426+00:00
-- url     : https://prove2.me/theorems/428452b0-d595-4ad3-8fe0-a2b0e2070520
-- title:
--   Lemma 3.4 — every ms-dimensional dual restriction has high border rank
-- statement:
--   Let $e\ge2$, $s=2e-1$, and $m\ge e^2$. Let $T_{e,m}$ be exactly the integer-entry tensor of equation (3.2), regarded over $\mathbb C$. For every subspace $W\subseteq(\mathbb C^{me^2})^*$ of dimension $ms$,
--
--   $$\underline R(T_{e,m}|_W)\ge s(me-m-e^2).$$
--
--   The quantifier includes all such dual subspaces, with no coordinate or genericity restriction. The right side is an integer expression, including its possible zero or negative values. This is the uniform restriction bound needed by border substitution.
--
--   Differences from the source:
--   - encoding: arbitrary finite-dimensional complex mode spaces → coordinate spaces with arbitrary natural dimensions; reason: choosing bases identifies every source instance with one of these arrays; tensors, dual subspaces, and Koszul maps are transported by those bases
--   - encoding: least rank in a complex limit → least r whose rank-at-most-r locus has the tensor in its topological closure; reason: finite complex product spaces are metrizable, so sequential limits and closure agree; approximants remain arbitrary complex tensors
--   - encoding: pair-indexed tensor and restriction to W → mixed-radix coordinates and a chosen basis of the entire subspace W; reason: the coordinate bijections and basis identify exactly the source tensor and restricted contraction; equality of block indices is never modulo me
--   - encoding: s(me−m−e²) → integer arithmetic for the full lower bound; reason: no truncation of either subtraction
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Lemma 3.4, p.9; §3 and §3.1 preambles pp.7,9; equation (3.2) p.9 (PDF same pages); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Construction

namespace ExplicitTensorBarrier694.Explicit

/-- Lovitz, STOC 2027 submission #694 (October 2026), Lemma 3.4, p.9.
Includes both Section 3 and Section 3.1 standing assumptions. The lower bound
uses integer arithmetic; negative right sides are not silently truncated. -/
theorem lemma_3_4 (e m : ℕ) (he : 2 ≤ e) (hm : e ^ 2 ≤ m)
    (W : Submodule ℂ (Fin (m * e ^ 2) → ℂ))
    (hW : Module.finrank ℂ W = m * (2 * e - 1)) :
    (2 * (e : ℤ) - 1) * ((m : ℤ) * (e : ℤ) - (m : ℤ) - (e : ℤ) ^ 2) ≤
      (borderRank (restrict (blockTensor e m) W) : ℤ) := by sorry

end ExplicitTensorBarrier694.Explicit
