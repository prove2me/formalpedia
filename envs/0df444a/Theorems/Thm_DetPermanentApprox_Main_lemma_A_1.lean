-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_A_1
-- name    : DetPermanentApprox.Main.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:31:13.445715+00:00
-- url     : https://prove2.me/theorems/b59f82b6-500f-4fe5-9e66-a83b17daa5bd
-- title:
--   Lemma A.1 — Gradient bound for both branches of Algorithm 2
-- statement:
--   Let $n\ge2$ and let $C,p,s$ satisfy the rounded-data conditions and the actual Section 4 parameters with $s\ge2$. In every executed round $0\le k<T$ of the explicit Algorithm 2, let $g_k$ be the ideal gradient selected by its degree-correction or objective branch. Then
--
--   $$\|g_k\|_2\le2\sqrt{2n}.$$
--
--   The branch is determined by the computed degree estimates at the actual iterate. The gradient bound is a conclusion for both branches, not an assumption on an arbitrary sequence.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - encoding: Algorithm 2 and the approximation procedures of Appendix A → the explicit Taylor approximation, first eligible vertex, nearest dyadic rounding with upward ties, and coordinatewise clipping; reason: these fix the permitted deterministic choices in the source procedure without assuming their accuracy
--   - generalization: C and p produced by Algorithm 1 preprocessing → any rational C and natural p satisfying RoundedData, with the same Section 4 parameters; reason: every source output satisfies RoundedData; the arguments on pp.21-30 use only its entry, grid, permanent and support properties, without the construction history or the least choice of p
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma A.1, p. 24 (PDF p. 24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Numerical
import Definitions.Def_DetPermanentApprox_Main_Analysis

namespace DetPermanentApprox.Main

theorem lemma_A_1 {n : ℕ} (hn : 2 ≤ n) (C : Matrix (Fin n) (Fin n) ℚ)
    (p s : ℕ) (hs : 2 ≤ s) (hC : RoundedData C p) (k : ℕ) (hk : k < iterationCount n p s) :
    Real.sqrt (squaredNorm (idealGradient C p s k)) ≤ 2 * Real.sqrt (2 * n) := by sorry

end DetPermanentApprox.Main
