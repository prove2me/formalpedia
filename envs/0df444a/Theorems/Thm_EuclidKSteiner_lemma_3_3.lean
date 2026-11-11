-- Prove2me | Theorems.Thm_EuclidKSteiner_lemma_3_3
-- name    : EuclidKSteiner.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:14:49.620605+00:00
-- url     : https://prove2.me/theorems/1b0d269e-97df-4f24-aaf9-88eebcac5f50
-- title:
--   Lemma 3.3 — threshold formula $w(\mathrm{MST}(H))=\int_0^\infty(\mathrm{cc}(H_{\le t})-1)\,dt$
-- statement:
--   Let $H$ be a finite connected multigraph with nonnegative edge weights, and for $t\ge0$ let $H_{\le t}$ be the spanning subgraph with all vertices of $H$ and exactly its edges of weight at most $t$. Then
--   $$w\bigl(\mathrm{MST}(H)\bigr)=\int_0^\infty\bigl(\mathrm{cc}(H_{\le t})-1\bigr)\,dt .$$
--
--   The formula turns MST weights into integrals of component counts; Lemmas 3.4, 3.5 and 3.10 are proved by comparing such integrals.
--
--   **Formalization Note** The integral is a lower Lebesgue integral of a nonnegative integer-valued function over $(0,\infty)$, compared with the (nonnegative) MST weight in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: a connected graph H → a connected finite multigraph (parallel edges and loops allowed); reason: the proof of Lemma 3.5 applies the formula to a contraction 'with parallel edges retained'; simple graphs are the special case
--   - encoding: ∫_0^∞ (cc(H≤t) − 1) dt → lower Lebesgue integral over (0, ∞) of the natural number cc − 1, equated with ENNReal.ofReal of the MST weight; reason: the integrand is nonnegative, so no integrability condition is needed; cc ≥ 1 on a nonempty graph
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 3.3, (3.2), p.10 (PDF p.12)

import Mathlib
import Definitions.Def_EuclidKSteiner_SpanningTree

namespace EuclidKSteiner

open scoped ENNReal

/-- **Lemma 3.3 (Threshold formula for MST weight).** Bhore, Kisfaludi-Bak, Marx, Odak,
*Parameterized Tractability of Euclidean k-Steiner Tree*, STOC 2027 submission (manuscript sha256
75361687…), Lemma 3.3, (3.2), p.10 (PDF p.12): "Let H be a connected graph with nonnegative edge
weights. Then w(MST(H)) = ∫_0^∞ (cc(H_{≤t}) − 1) dt."

For a finite connected multigraph `H` (vertex type `V`, edges `ι` with endpoints `ends` and weights
`wt ≥ 0`),
`w(MST(H)) = ∫_0^∞ (cc(H_{≤t}) − 1) dt`, where `H_{≤t}` keeps all vertices and the edges of weight at
most `t`.

**Formalization Note** Stated for multigraphs (parallel edges and loops allowed), as the proof of
Lemma 3.5 applies it to a contraction "with parallel edges retained". The integral is a lower
Lebesgue integral of a nonnegative integer-valued function over `(0, ∞)` (the point `0` has measure
zero), and the MST weight, which is nonnegative, is compared through `ENNReal.ofReal`; no
integrability hypothesis is involved. -/
theorem lemma_3_3 {V ι : Type*} [Fintype V] [Fintype ι] (ends : ι → Sym2 V) (wt : ι → ℝ)
    (hw : ∀ i, 0 ≤ wt i) (hconn : (SimpleGraph.fromEdgeSet (Set.range ends)).Connected) :
    ENNReal.ofReal (mstWeightOn (Finset.univ : Finset V) ends Finset.univ wt) =
      ∫⁻ t in Set.Ioi (0 : ℝ),
        ((numComponents ends (thresholdEdges Finset.univ wt t) - 1 : ℕ) : ℝ≥0∞) := by sorry

end EuclidKSteiner
