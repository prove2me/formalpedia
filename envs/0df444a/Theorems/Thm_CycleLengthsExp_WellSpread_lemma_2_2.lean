-- Prove2me | Theorems.Thm_CycleLengthsExp_WellSpread_lemma_2_2
-- name    : CycleLengthsExp.WellSpread.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:17.263107+00:00
-- url     : https://prove2.me/theorems/4ec46f44-9ede-4dc5-a8b1-c9264d118c40
-- title:
--   Lemma 2.2, p. 5 — deleting ϵn vertices from a (k,α)-expander leaves a (k,α/2)-expander on (1−3ϵ/α)n vertices
-- statement:
--   Let $0<\alpha\le1$ and $k>0$, and let $G=(V,E)$ be a $(k,\alpha)$-expander on $n$ vertices. Let $V_0\subseteq V$ have $|V_0|\le\epsilon n$, where
--
--   $$0<\epsilon\le\frac{\alpha^2k}{8n}.$$
--
--   Then there is a vertex set $U\subseteq V\setminus V_0$ with
--
--   $$|U|\ \ge\ \Bigl(1-\frac{3\epsilon}{\alpha}\Bigr)n$$
--
--   such that the induced graph $G[U]$ is a $(k,\alpha/2)$-expander.
--
--   Expansion is robust: deleting a small set costs only a small set more and halves the expansion ratio. The proof of Theorem 1 applies it to delete a breadth-first tree from the expander.
--
--   **Formalization Note.** $G[U]$ is `G.induce U`, a graph on the subtype $U$ with the edges of $G$. At $n=0$ the hypothesis on $\epsilon$ is unsatisfiable (Lean reads $x/0=0$), as in the source, where $n\ge1$.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 5, Lemma 2.2

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

namespace CycleLengthsExp.WellSpread

theorem lemma_2_2 (n : ℕ) (G : SimpleGraph (Fin n)) (k α ε : ℝ)
    (hk : 0 < k) (hα0 : 0 < α) (hα1 : α ≤ 1) (hG : IsKAlphaExpander k α G)
    (V₀ : Set (Fin n)) (hV₀ : (V₀.ncard : ℝ) ≤ ε * n)
    (hε0 : 0 < ε) (hε1 : ε ≤ α ^ 2 * k / (8 * n)) :
    ∃ U : Set (Fin n), U ⊆ V₀ᶜ ∧ (1 - 3 * ε / α) * n ≤ (U.ncard : ℝ) ∧
      IsKAlphaExpander k (α / 2) (G.induce U) := by sorry

end CycleLengthsExp.WellSpread
