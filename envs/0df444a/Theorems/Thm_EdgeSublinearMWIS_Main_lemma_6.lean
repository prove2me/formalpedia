-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_lemma_6
-- name    : EdgeSublinearMWIS.Main.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:45:43.238766+00:00
-- url     : https://prove2.me/theorems/ee576a44-36c3-4f8f-81bb-291d5137f6e3
-- title:
--   Lemma 6 — deterministic light balanced separator
-- statement:
--   Fix a strongly edge-sublinear hereditary class and an integer $a\ge2$ satisfying the uniform treewidth bound (2). There is a single finite separator program, a positive integer coefficient $B$, a polynomial runtime and $D>0$ such that, for $n\ge2$ and rational $0<\delta<1$, its threshold $p(n,\delta)$ is positive, nondecreasing in $n$, and
--   $$p(n,\delta)\le D(\delta^{-1}\log_2n)^{4a-2}.$$
--   On a promised induced input $G[W]$ with rational $x\in[0,1]^W$, $k=x(W)\ge p(|W|,\delta)$ and $e_{G[W]}(x)\le k^2/p(|W|,\delta)$, the program returns a balanced $S\subseteq W$ with $x(S)\le\delta k$ in polynomial input-bit time. Original labels and optional ambient graph padding are preserved. Taking $W=V(G)$ gives exactly the stated source result. No separator oracle is supplied.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: a deterministic polynomial-time algorithm on rational inputs → one finite program, serialized rational inputs and actual halting-step bounds; reason: binary conventions fix a computational model without restricting rational values
--   - encoding: an unspecified class-uniform threshold p=O_C((delta inverse log n)^(4a-2)), nondecreasing in n → max(1,ceil(B (h(n)/delta)^(4a-2))) for one positive integer B before all inputs; reason: p may be enlarged by the p.11 monotonicity argument; h(n) is within universal constant factors of log_2 n
--   - encoding: an input graph, including each recursive induced subgraph → an active induced set W in an ambient labeled graph; reason: labels are retained for recursive calls and padded input work remains polynomial; W=V gives every standalone instance
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Lemma 6, p.6 (PDF p.6), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts

namespace EdgeSublinearMWIS.Main

theorem lemma_6 (C : GraphClass) (a : ℕ) (K : ℝ)
    (separatorClass : StronglyEdgeSublinear C) (ha : 2 ≤ a) (bound : TreewidthBound C a K) :
    ∃ (B : ℕ) (D : ℝ) (M : Program) (time : Polynomial ℕ), 0 < B ∧ 0 < D ∧
      (∀ (n : ℕ) (δ : ℚ), 2 ≤ n → 0 < δ → δ < 1 →
        (threshold B a n δ : ℝ) ≤ D * ((δ : ℝ)⁻¹ * logTwo n) ^ (4 * a - 2)) ∧
      (∀ (n m : ℕ) (δ : ℚ), 2 ≤ m → m ≤ n → 0 < δ → δ < 1 →
        threshold B a m δ ≤ threshold B a n δ) ∧
      SeparatorContract C a B M time := by sorry

end EdgeSublinearMWIS.Main
