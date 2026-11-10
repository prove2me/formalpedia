-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_outer_soundness
-- name    : BhangaleHypergraph.Main.outer_soundness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:06:02.261897+00:00
-- url     : https://prove2.me/theorems/f9b4fa36-ff22-4f67-9fc8-e5b6f4c6ec09
-- title:
--   Lemma 2.7 — Pairwise outer soundness
-- statement:
--   Suppose the neighborhood construction from a biregular base instance $L$ produces nonempty local alphabets and its edge-sampling law is defined. For every simultaneous multilayer labeling $\Lambda$ and every $i<j$,
--   $$\Pr_{e^*\sim\mu_{ij}}[\Lambda\text{ satisfies }e^*]\le\operatorname{val}(L).$$
--   The marginal comes from a uniform right vertex and independent incident occurrences with replacement. It retains multiplicity even when distinct occurrences have identical endpoints or projection tables.
--
--   This is the exact pairwise soundness guarantee used by the outer verifier.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
--   - encoding: enumerated local labels and the marginal μᵢⱼ → normalized local assignments and the finite sum over right vertices and two incident occurrences; reason: the distribution is the same experiment; zero edges are explicitly outside its successful sampling branch
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 2.7, p. 8 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Base

namespace BhangaleHypergraph.Main

theorem outer_soundness (B : BaseCover) (ell : ℕ) (hell : 2 ≤ ell)
    (hproduced : NeighborhoodProduced B ell) (σ : NeighborhoodLabeling B ell) (i j : Fin ell) (hij : i < j) :
    NeighborhoodPairValue B σ i j ≤ BaseValue B := by sorry

end BhangaleHypergraph.Main
