-- Prove2me | Theorems.Thm_CycleLengthsExp_WellSpread_lemma_2_6
-- name    : CycleLengthsExp.WellSpread.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:05.031865+00:00
-- url     : https://prove2.me/theorems/d3cbb6db-76ee-479c-b0e7-110eb13fc529
-- title:
--   Lemma 2.6, p. 6 — a set W with |W| > n/2 and small boundary contains a ((1/2−2ϵ)n, α/2)-expander on > (1/2−2ϵ)n vertices
-- statement:
--   Let $\alpha>0$ and let $G=(V,E)$ be an $\alpha$-expander on $n$ vertices. Let $W\subseteq V$ with $|W|>n/2$ and $|N_G(W)|\le\alpha\epsilon n$, where $0<\epsilon<1/4$. Then there is $U\subseteq W$ with
--
--   $$|U|\ >\ \Bigl(\frac12-2\epsilon\Bigr)n$$
--
--   such that the induced graph $G[U]$ is a $\bigl((\tfrac12-2\epsilon)n,\ \alpha/2\bigr)$-expander.
--
--   It is the step of Lemma 2.7 that extracts an expander from the middle levels of a bounded-degree breadth-first tree.
--
--   **Formalization Note.** $G[U]$ is `G.induce U`, with the edges of $G$. The page states $\alpha>0$ in the definition of an $\alpha$-expander; it is a hypothesis here.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 6, Lemma 2.6

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

namespace CycleLengthsExp.WellSpread

theorem lemma_2_6 (n : ℕ) (G : SimpleGraph (Fin n)) (α ε : ℝ) (hα : 0 < α)
    (hG : IsAlphaExpander α G) (W : Set (Fin n))
    (hW : (n : ℝ) / 2 < (W.ncard : ℝ)) (hNW : ((extNbhd G W).ncard : ℝ) ≤ α * ε * n)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 4) :
    ∃ U : Set (Fin n), U ⊆ W ∧ (1 / 2 - 2 * ε) * n < (U.ncard : ℝ) ∧
      IsKAlphaExpander ((1 / 2 - 2 * ε) * n) (α / 2) (G.induce U) := by sorry

end CycleLengthsExp.WellSpread
