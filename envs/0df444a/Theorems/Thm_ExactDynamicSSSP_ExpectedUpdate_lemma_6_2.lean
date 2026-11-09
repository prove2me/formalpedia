-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_6_2
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:38:44.862613+00:00
-- url     : https://prove2.me/theorems/05ffa4d6-eb5f-4ef7-ac40-7c303c3295af
-- title:
--   Lemma 6.2 — subtree double counting
-- statement:
--   Let $G$ be a fixed weighted digraph with $j\ge1$ arcs, $s$ a source and $\mathrm{par}$ any shortest-path tree of $G$ rooted at $s$, with $H_x$ the depth of $x$ ($0$ if unreachable). For a uniformly chosen existing arc $e$,
--   $$\mathbb E_e\,q(e)=\frac1j\sum_xH_x,\qquad \mathbb E_e\,f^+(e)=\frac1j\sum_xD^+_xH_x,\qquad \mathbb E_e\,f^-(e)=\frac1j\sum_xD^-_xH_x. \tag{5}$$
--
--   Each reachable vertex is counted once for each of its non-root ancestors, itself included.
--
--   Differences from the source:
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 6.2, equation (5), PDF p.8 = printed p.8

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 6.2 (PDF p. 8), eq. (5). For a fixed weighted graph with `j ≥ 1` arcs and any of its
shortest-path trees, a uniformly chosen existing arc `e` satisfies
`𝔼_e q(e) = (1/j) Σ_x H_x` and `𝔼_e f^±(e) = (1/j) Σ_x D^±_x H_x`. -/
theorem lemma_6_2 {n : ℕ} (G : WDigraph n) (s : Fin n) (par : Fin n → Option (Fin n))
    (hT : IsSPT G s par) (hj : 1 ≤ G.numArcs) :
    arcAverage G (subtreeSize s par) =
        (G.numArcs : ℝ≥0∞)⁻¹ * ∑ x, (treeDepth par s x : ℝ≥0∞) ∧
    arcAverage G (subtreeOut G s par) =
        (G.numArcs : ℝ≥0∞)⁻¹ * ∑ x, (G.outDeg x : ℝ≥0∞) * (treeDepth par s x : ℝ≥0∞) ∧
    arcAverage G (subtreeIn G s par) =
        (G.numArcs : ℝ≥0∞)⁻¹ * ∑ x, (G.inDeg x : ℝ≥0∞) * (treeDepth par s x : ℝ≥0∞) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
