-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_Supplement_lemma_5_2
-- name    : BourgainUnion.Euclidean.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:35:44.159756+00:00
-- url     : https://prove2.me/theorems/2bc3e1a7-bf24-431e-a1d5-cc50a0a9fef7
-- title:
--   Lemma 5.2 — the norm of a projection onto the cycle space
-- statement:
--   Let $G=(V,E)$ be a connected simple graph with $n$ vertices, $m$ edges and girth $g$, with cycle-space dimension $r=m-n+1>0$ and an arbitrary orientation. Let $Z\subseteq\mathbb R^E$ be its cycle space and $W=\mathbb R^E$ with the norm (20). For every linear map $P:\mathbb R^E\to Z$ fixing $Z$,
--   $$\|P\|_{W\to Z}=\max\Bigl\{1,\ \sqrt g\,\max_{e\in E}\|Pe\|_2\Bigr\},$$
--   where $e$ also denotes the indicator vector of the edge. As a consequence,
--   $$\max\bigl\{1,\sqrt{gr/m}\bigr\}\le\lambda(Z,W)\le\sqrt g .$$
--
--   Differences from the source:
--   - encoding: a connected graph G = (V, E) with an arbitrary fixed orientation, and ℝ^E → a Mathlib SimpleGraph on a Fintype V, an Orientation picking one dart per edge, and functions G.edgeSet → ℝ; reason: the dart fixes tail and head; every orientation of the simple graph arises
--   - encoding: r = m − n + 1 > 0 → n ≤ m, with r computed as the natural number m + 1 − n; reason: n ≤ m is r > 0; the subtraction never truncates under it
--   - encoding: girth g ≥ 3 → g = SimpleGraph.girth G, with no separate hypothesis; reason: a connected simple graph with n ≤ m has a cycle, so its girth is at least 3 (Mathlib three_le_girth); the hypothesis would be redundant
--   - encoding: ‖P‖_{W→Z} = sup_{w≠0} ‖Pw‖/‖w‖_W and λ(Z, W) = inf over P ∈ 𝒫, with Z carrying the norm inherited from W → opNormW (sup of ‖Pw‖_W/‖w‖_W over w ≠ 0) and projConst (inf over projections) in ℝ≥0∞; reason: the ℝ≥0∞ sup/inf has no junk value; the target norm is the inherited ‖·‖_W exactly as defined on p. 23
--   - encoding: linear maps P : ℝ^E → Z with P|_Z = I_Z → linear endomorphisms of ℝ^E with range in Z that fix Z pointwise; reason: composing with the inclusion Z ⊆ ℝ^E is a bijection between the two families and preserves every norm
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 24, §5.3, Lemma 5.2 (setting §§5.1–5.2, pp. 23–24)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_Supplement_CycleSpaceModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

/-- Lemma 5.2, p. 24: the norm formula for every `P ∈ 𝒫` and the two bounds on `λ(Z, W)`,
with `n` vertices, `m` edges, girth `g` and `r = m − n + 1 > 0`. -/
theorem lemma_5_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected)
    (hr : Fintype.card V ≤ G.edgeFinset.card) (O : Orientation G) :
    (∀ P : (G.edgeSet → ℝ) →ₗ[ℝ] (G.edgeSet → ℝ), IsCycleProjection O P →
      opNormW O P = ENNReal.ofReal (max 1
        (Real.sqrt (G.girth : ℝ) * ⨆ e : G.edgeSet, l2 (P (edgeVec e))))) ∧
    ENNReal.ofReal (max 1 (Real.sqrt ((G.girth : ℝ) *
        ((G.edgeFinset.card + 1 - Fintype.card V : ℕ) : ℝ) / (G.edgeFinset.card : ℝ)))) ≤
      projConst O ∧
    projConst O ≤ ENNReal.ofReal (Real.sqrt (G.girth : ℝ)) := by sorry

end BourgainUnion.Euclidean.Supplement
