-- Prove2me | Theorems.Thm_DoublingMST_lemma_3_2
-- name    : DoublingMST.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:32:32.542794+00:00
-- url     : https://prove2.me/theorems/4b324001-958c-455e-be96-d1bd63ba921f
-- title:
--   Lemma 3.2 — a WSPC captures every MST
-- statement:
--   Let $(X,d)$ be a metric space with $|X|=n\ge2$, let $t\ge2$ and let $\Phi$ be a $t$-WSPC of $X$. For every minimum spanning tree $T^*$ of $X$:
--
--   1. for every $(U,V)\in\Phi$, at most one edge of $T^*$ lies in $U\times V=\{\{a,b\}:a\in U,b\in V,a\ne b\}$;
--   2. for every assignment of a pair $(U_e,V_e)\in\Phi$ with $e\in U_e\times V_e$ to each edge $e$ of $T^*$, and every choice of points $p_e\in U_e$, $q_e\in V_e$, the edges $\{p_e,q_e\}$ are $n-1$ distinct edges forming a spanning tree of $X$.
--
--   This is the bridge from a pair cover to an approximate MST: one representative edge per pair suffices.
--
--   Differences from the source:
--
--   - encoding: an n-point metric space (X, d) → points Fin n with d : Fin n → Fin n → ℝ satisfying IsMetric; reason: finite metric spaces up to relabelling; same instances
--   - encoding: the standing assumption |X| ≥ 2 of §2 (p.11) → hypothesis 2 ≤ n on the number of points; reason: the source assumes it throughout; it excludes only the one-point space
--   - reading: the MST of X → every minimum spanning tree T* of X; reason: the source writes "the MST" without assuming uniqueness; the proof uses only minimality
--   - encoding: U × V (footnote 3: unordered cross pairs with a ≠ b) → edges s(a, b) with a ∈ U, b ∈ V, a ≠ b; reason: footnote 3, p.14
--   - encoding: {(p_i, q_i)}_{i=1}^{n−1} forms a spanning tree → the image of T* under e ↦ {p_e, q_e} has |T*| elements and is a spanning tree; reason: the n − 1 pairs are distinct exactly when the image has n − 1 elements
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 3.2, p.14 (PDF p.16); proof in Appendix C

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_IsWSPC
import Definitions.Def_DoublingMST_completeGraph
import Definitions.Def_DoublingMST_edgeCost
import Definitions.Def_CombOpt_SpanningTree_Graph_IsMST
open scoped Classical

namespace DoublingMST

/-- **Lemma 3.2 (a WSPC captures the MST).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 3.2, p.14 (PDF p.16): "Given a metric space (X, d) with |X| = n and a t-WSPC Φ for
t ≥ 2: (1) For every pair (U, V) ∈ Φ, there is at most one edge of U × V in the MST of X. (2) For
each MST edge e*_i, let (U_i, V_i) ∈ Φ be an arbitrary pair that contains e*_i, and let (p_i, q_i) be
an arbitrary pair of points from (U_i, V_i). Then {(p_i, q_i)}_{i=1}^{n−1} forms a spanning tree of X."
Footnote 3: "A × B := {{a, b} : a ∈ A, b ∈ B, a ≠ b}."

For a metric on `n ≥ 2` points, `t ≥ 2` and a t-WSPC `Φ`, and for **every** MST `T*`:
1. each `(U, V) ∈ Φ` has at most one edge of `T*` in `U × V`;
2. for every assignment `e ↦ (U_e, V_e) ∈ Φ` with `e ∈ U_e × V_e` on the edges of `T*`, and every
   choice `e ↦ (p_e, q_e) ∈ U_e × V_e`, the pairs `{p_e, q_e}` are `n − 1` distinct edges forming a
   spanning tree of `X`.

**Formalization Note.** "The MST" is read as every MST (`CombOpt.SpanningTree.Graph.IsMST` on the
complete graph with weights `d`). `U × V` is the set of unordered cross pairs of footnote 3. -/
theorem lemma_3_2 : ∀ (n : ℕ), 2 ≤ n → ∀ d : Fin n → Fin n → ℝ, IsMetric d →
    ∀ (t : ℝ), 2 ≤ t → ∀ Φ : Finset (Finset (Fin n) × Finset (Fin n)), IsWSPC d Φ t →
      ∀ Tstar : Finset (Sym2 (Fin n)), (completeGraph n).IsMST (edgeCost d) Tstar →
        (∀ UV ∈ Φ, (Tstar.filter fun e =>
            ∃ a ∈ UV.1, ∃ b ∈ UV.2, a ≠ b ∧ e = s(a, b)).card ≤ 1) ∧
        ∀ (f : Sym2 (Fin n) → Finset (Fin n) × Finset (Fin n)) (g : Sym2 (Fin n) → Fin n × Fin n),
          (∀ e ∈ Tstar, f e ∈ Φ ∧ ∃ a ∈ (f e).1, ∃ b ∈ (f e).2, a ≠ b ∧ e = s(a, b)) →
          (∀ e ∈ Tstar, (g e).1 ∈ (f e).1 ∧ (g e).2 ∈ (f e).2) →
          (Tstar.image fun e => s((g e).1, (g e).2)).card = Tstar.card ∧
          (completeGraph n).IsSpanningTree (Tstar.image fun e => s((g e).1, (g e).2)) := by sorry

end DoublingMST
