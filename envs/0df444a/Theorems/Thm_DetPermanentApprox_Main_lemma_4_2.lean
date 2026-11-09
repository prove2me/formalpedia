-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_4_2
-- name    : DetPermanentApprox.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:30:54.885327+00:00
-- url     : https://prove2.me/theorems/1941ce26-acc6-4013-9433-215661748a98
-- title:
--   Lemma 4.2 — Bounded entropy-dual minimizer
-- statement:
--   Let $n\ge2$ and let $C$ be any rational matrix satisfying the rounded-data conditions of Section 4: entries in $[0,1]$ on the $2^{-p}$ grid, permanent at least one, and every positive edge in a perfect matching. For $s\ge2$, use exactly the parameters in (4.1), with $t=1-\delta$. There exists a global minimizer $\theta^*$ of $\Phi_{C,t}$ with
--
--   $$\|\theta^*\|_\infty\le R_0=\frac{2n^2(n+p)}{\delta}.$$
--
--   This is an existence statement for a bounded representative. It places no bound on every minimizer, since the bipartite gauge shifts need not be bounded.
--
--   Differences from the source:
--   - encoding: finite labelled matrix, graph, and coordinate sets → Fin n or arbitrary finite types with explicit row and column copies; reason: finite enumerations and reindexing preserve every source instance
--   - generalization: C and p produced by Algorithm 1 preprocessing → any rational C and natural p satisfying RoundedData, with the same Section 4 parameters; reason: every source output satisfies RoundedData; the arguments on pp.21-30 use only its entry, grid, permanent and support properties, without the construction history or the least choice of p
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma 4.2, p. 21 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Numerical
import Definitions.Def_DetPermanentApprox_Main_Analysis

namespace DetPermanentApprox.Main

theorem lemma_4_2 {n : ℕ} (hn : 2 ≤ n) (C : Matrix (Fin n) (Fin n) ℚ)
    (p s : ℕ) (hs : 2 ≤ s) (hC : RoundedData C p) :
    ∃ θ : Vertex n → ℝ, IsMinimizer (Phi (realMatrix C) (targetMarginal s : ℝ)) θ ∧
      θ ∈ box n p s := by sorry

end DetPermanentApprox.Main
