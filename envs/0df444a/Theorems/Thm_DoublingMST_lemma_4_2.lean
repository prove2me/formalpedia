-- Prove2me | Theorems.Thm_DoublingMST_lemma_4_2
-- name    : DoublingMST.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:31:51.41139+00:00
-- url     : https://prove2.me/theorems/41ea186b-c17b-4ed3-91c0-8fae6d5c252a
-- title:
--   Lemma 4.2 — local MST lower bound
-- statement:
--   Let $(X,d)$ be a metric space with $|X|\ge2$ and let $T^*$ be any minimum spanning tree of $X$. Let $A\subseteq X$, $\rho>0$, and let $N\subseteq A$ be $\rho$-packing with $|N|\ge2$. Then
--
--   $$w\bigl(B(A,\operatorname{diam}(A))\cap T^*\bigr)\ge\frac{\rho\,|N|}{2},$$
--
--   where $P\cap T^*$ is the set of edges of $T^*$ with at least one endpoint in $P$.
--
--   The lemma charges approximation error to the MST weight near a set.
--
--   Differences from the source:
--
--   - encoding: an n-point metric space (X, d) → points Fin n with d : Fin n → Fin n → ℝ satisfying IsMetric; reason: finite metric spaces up to relabelling; same instances
--   - encoding: the standing assumption |X| ≥ 2 of §2 (p.11) → hypothesis 2 ≤ n on the number of points; reason: the source assumes it throughout; it excludes only the one-point space
--   - reading: the MST T* of X → every minimum spanning tree T* of X; reason: the source writes "the MST" without assuming uniqueness; the proof uses only that T* is a spanning tree of weight MST(X)
--   - encoding: ρ-packing for A (Definition 2.3, ρ > 0) → N ⊆ A, 0 < ρ and IsPacking d N ρ; reason: Definition 2.3
--   - generalization: §2.2 (p.13): "we can assume henceforth that the minimum interpoint distance of X is greater than 1 and the diameter of X is ∆ ≤ n^{10}/ϵ" → every metric on n ≥ 2 points, with neither normalization; reason: the proof (pp.19–20) uses only the triangle inequality and the tree, and the statement specializes to the source's by adding the two assumptions
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 4.2, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_IsPacking
import Definitions.Def_DoublingMST_diam
import Definitions.Def_DoublingMST_nbhd
import Definitions.Def_DoublingMST_edgesNear
import Definitions.Def_DoublingMST_treeWeight
import Definitions.Def_DoublingMST_completeGraph
import Definitions.Def_CombOpt_SpanningTree_Graph_IsMST
open scoped Classical

namespace DoublingMST

/-- **Lemma 4.2 (local MST lower bound).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 4.2, p.19 (PDF p.21): "Let T* be the MST of X. Let A ⊆ X be an arbitrary subset and
N ⊆ A be ρ-packing for A. If |N| ≥ 2, then w(B(A, diam(A)) ∩ T*) ≥ ρ|N|/2."

For a metric on `n ≥ 2` points, **every** MST `T*`, every `A ⊆ X`, every `ρ > 0` and every
ρ-packing `N ⊆ A` with `|N| ≥ 2`:
$$w\bigl(B(A, \operatorname{diam}(A)) \cap T^*\bigr) \ge \rho |N| / 2,$$
where `P ∩ T*` is the set of edges of `T*` with an endpoint in `P` (`edgesNear`).

**Formalization Note.** "The MST" is read as every MST. `ρ > 0` is Definition 2.3's range. -/
theorem lemma_4_2 : ∀ (n : ℕ), 2 ≤ n → ∀ d : Fin n → Fin n → ℝ, IsMetric d →
    ∀ Tstar : Finset (Sym2 (Fin n)), (completeGraph n).IsMST (edgeCost d) Tstar →
    ∀ (A N : Finset (Fin n)) (ρ : ℝ), 0 < ρ → N ⊆ A → IsPacking d N ρ → 2 ≤ N.card →
      ρ * N.card / 2 ≤ treeWeight d (edgesNear (nbhd d A (diam d A)) Tstar) := by sorry

end DoublingMST
