-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_Supplement_theorem_5_3
-- name    : BourgainUnion.Euclidean.Supplement.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:36:18.130245+00:00
-- url     : https://prove2.me/theorems/cffba064-bdb9-439e-83a7-54dd080b6fc6
-- title:
--   Theorem 5.3 — from projection constant to Lipschitz constant
-- statement:
--   Let $G=(V,E)$ be a connected simple graph with $n$ vertices, $m$ edges, girth $g$, $r=m-n+1>0$ and an arbitrary orientation; let $T$ be a spanning tree with root $o$ and depth $D$, and let $N\ge1$ be an integer. With $X_N$, $A_N$ and $e(A_N)$ as in Section 5.4 and $\beta_N=2D/(2N-1)$,
--   $$\max\Bigl\{1,\frac{\lambda(Z,W)}{1+\beta_N}\Bigr\}\le e(A_N)\le\lambda(Z,W). \tag{21}$$
--   In particular, if $N\ge D+1$ then
--   $$e(A_N)\ge\frac12\sqrt{gr/m}.$$
--
--   Differences from the source:
--   - encoding: a connected graph G = (V, E) with an arbitrary fixed orientation, and ℝ^E → a Mathlib SimpleGraph on a Fintype V, an Orientation picking one dart per edge, and functions G.edgeSet → ℝ; reason: the dart fixes tail and head; every orientation of the simple graph arises
--   - encoding: r = m − n + 1 > 0 → n ≤ m, with r computed as the natural number m + 1 − n; reason: n ≤ m is r > 0; the subtraction never truncates under it
--   - encoding: girth g ≥ 3 → g = SimpleGraph.girth G, with no separate hypothesis; reason: a connected simple graph with n ≤ m has a cycle, so its girth is at least 3 (Mathlib three_le_girth); the hypothesis would be redundant
--   - encoding: G connected, with a spanning tree T of depth D rooted at o → a SimpleGraph T ≤ G with T.IsTree on all of V, root o, and D = max_v dist_T(o, v); no separate connectivity hypothesis; reason: a spanning tree of G makes G connected, so the hypothesis would be redundant
--   - encoding: non-tree edges e_1, …, e_r and a ∈ ℤ^r → the subtype of non-tree edges as index type, a : NonTree → ℤ; reason: there are exactly r non-tree edges; this is a relabeling of the coordinates
--   - encoding: e(A_N), the optimal Lipschitz constant of an extension F : X_N → Z of ϕ(Ca) = Ca → cellExtConst in ℝ≥0∞: the infimum of L ≥ 0 such that some total map, Z-valued on X_N and the identity on A_N, is L-Lipschitz for ‖·‖_W on X_N; reason: values off X_N are irrelevant; Z carries the norm inherited from W; no junk value
--   - encoding: ‖P‖_{W→Z} = sup_{w≠0} ‖Pw‖/‖w‖_W and λ(Z, W) = inf over P ∈ 𝒫, with Z carrying the norm inherited from W → opNormW (sup of ‖Pw‖_W/‖w‖_W over w ≠ 0) and projConst (inf over projections) in ℝ≥0∞; reason: the ℝ≥0∞ sup/inf has no junk value; the target norm is the inherited ‖·‖_W exactly as defined on p. 23
--   - encoding: linear maps P : ℝ^E → Z with P|_Z = I_Z → linear endomorphisms of ℝ^E with range in Z that fix Z pointwise; reason: composing with the inclusion Z ⊆ ℝ^E is a bijection between the two families and preserves every norm
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 24, §5.4, Theorem 5.3, inequality (21) (setting §§5.1–5.4, pp. 23–24)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_Supplement_CycleSpaceModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

/-- Theorem 5.3, p. 24: both inequalities of (21) for every `N ≥ 1`, and the clause
`N ≥ D + 1 → e(A_N) ≥ ½√(gr/m)`; `D` is the depth of the spanning tree `T` from the root `o`. -/
theorem theorem_5_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hr : Fintype.card V ≤ G.edgeFinset.card) (O : Orientation G)
    (T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree) (o : V) (N : ℕ) (hN : 1 ≤ N) :
    max 1 (projConst O /
        ENNReal.ofReal (1 + 2 * (treeDepth T o : ℝ) / (2 * (N : ℝ) - 1))) ≤
      cellExtConst O hTG hT o N ∧
    cellExtConst O hTG hT o N ≤ projConst O ∧
    (treeDepth T o + 1 ≤ N →
      ENNReal.ofReal ((1/2) * Real.sqrt ((G.girth : ℝ) *
        ((G.edgeFinset.card + 1 - Fintype.card V : ℕ) : ℝ) / (G.edgeFinset.card : ℝ))) ≤
        cellExtConst O hTG hT o N) := by sorry

end BourgainUnion.Euclidean.Supplement
