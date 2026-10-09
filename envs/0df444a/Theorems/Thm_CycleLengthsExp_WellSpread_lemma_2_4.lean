-- Prove2me | Theorems.Thm_CycleLengthsExp_WellSpread_lemma_2_4
-- name    : CycleLengthsExp.WellSpread.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:02.280742+00:00
-- url     : https://prove2.me/theorems/f246be6f-559d-47fe-a8fd-7c5d6c18d57e
-- title:
--   Lemma 2.4, p. 6 — contracting parts of size ≤ C gives a (k/C, α/C)-expander on r ≥ n/C vertices
-- statement:
--   Let $k>0$, $\alpha>0$, $C>0$, and let $G=(V,E)$ be a $(k,\alpha)$-expander on $n$ vertices. Let $V_1,\dots,V_r$ be disjoint non-empty vertex sets, each of size at most $C$, with $V=\bigcup_{i=1}^r V_i$. Let $G'$ be the graph on $\{1,\dots,r\}$ obtained by contracting each $V_i$ to a vertex: $i\ne j$ are adjacent when some edge of $G$ joins $V_i$ and $V_j$. Then
--
--   $$r\ \ge\ \frac nC\qquad\text{and}\qquad G' \text{ is a } \Bigl(\frac kC,\frac\alpha C\Bigr)\text{-expander}.$$
--
--   In the proof of Theorem 1 it turns subtrees of bounded size into single vertices, so that a long path can be found in the contracted graph.
--
--   **Formalization Note.** The partition is a surjection $f:V\to\{1,\dots,r\}$ with $V_i=f^{-1}(i)$; surjectivity is the non-emptiness of the parts. The contracted graph has no loops.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 6, Lemma 2.4

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

namespace CycleLengthsExp.WellSpread

theorem lemma_2_4 (n r : ℕ) (G : SimpleGraph (Fin n)) (k α C : ℝ)
    (hk : 0 < k) (hα : 0 < α) (hC : 0 < C) (hG : IsKAlphaExpander k α G)
    (f : Fin n → Fin r) (hf : Function.Surjective f)
    (hfib : ∀ i : Fin r, ((f ⁻¹' {i}).ncard : ℝ) ≤ C) :
    (n : ℝ) / C ≤ r ∧ IsKAlphaExpander (k / C) (α / C) (contract G f) := by sorry

end CycleLengthsExp.WellSpread
