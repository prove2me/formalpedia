-- Prove2me | Theorems.Thm_CycleLengthsExp_WellSpread_lemma_2_3
-- name    : CycleLengthsExp.WellSpread.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:33.093069+00:00
-- url     : https://prove2.me/theorems/d526dfbc-a34e-4596-93a5-de1e4e5cb8c5
-- title:
--   Lemma 2.3, p. 5 — an α-expander has tα/(1+α) vertex-disjoint paths between any two sets of size ≥ t
-- statement:
--   Let $\alpha>0$ and let $G=(V,E)$ be an $\alpha$-expander on $n$ vertices. Let $A,B\subseteq V$ with $|A|,|B|\ge t$ for some real $t>0$. Then $G$ contains $m$ pairwise vertex-disjoint paths $P_1,\dots,P_m$, each starting in $A$ and ending in $B$, with
--
--   $$m\ \ge\ \frac{t\alpha}{1+\alpha}.$$
--
--   This is the connectivity input to Theorem 1: it supplies many short disjoint connections between the first breadth-first tree and the expander found inside the second one.
--
--   **Formalization Note.** A path is a walk with no repeated vertex; a path may consist of one vertex of $A\cap B$. Vertex-disjoint means the vertex sets (supports) of distinct paths are disjoint, endpoints included.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 5, Lemma 2.3

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

namespace CycleLengthsExp.WellSpread

theorem lemma_2_3 (n : ℕ) (G : SimpleGraph (Fin n)) (α : ℝ) (hα : 0 < α)
    (hG : IsAlphaExpander α G) (A B : Set (Fin n)) (t : ℝ) (ht : 0 < t)
    (hA : t ≤ (A.ncard : ℝ)) (hB : t ≤ (B.ncard : ℝ)) :
    ∃ (m : ℕ) (a b : Fin m → Fin n) (P : ∀ i, G.Walk (a i) (b i)),
      t * α / (1 + α) ≤ (m : ℝ) ∧
      (∀ i, a i ∈ A ∧ b i ∈ B ∧ (P i).IsPath) ∧
      ∀ i j, i ≠ j → ∀ x, x ∈ (P i).support → x ∉ (P j).support := by sorry

end CycleLengthsExp.WellSpread
