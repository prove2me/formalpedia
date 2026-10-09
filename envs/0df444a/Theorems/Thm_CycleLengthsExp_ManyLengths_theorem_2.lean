-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_theorem_2
-- name    : CycleLengthsExp.ManyLengths.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:51.586557+00:00
-- url     : https://prove2.me/theorems/3ede001e-4457-441c-8fe4-434ac2135ff1
-- title:
--   Theorem 2 — α-expanders have Ω(α³/log(1/α))n cycle lengths
-- statement:
--   There is an absolute constant $c>0$ such that, for every $0<\alpha\le1$, all sufficiently large $n$, and every $\alpha$-expander $G$ on $n$ vertices,
--   $$|L(G)|\ge c\,\frac{\alpha^3}{\log_2(2/\alpha)}\,n.$$
--   Here $L(G)$ is the set of lengths of simple cycles of $G$, so the inequality counts distinct lengths rather than cycles.
--
--   The theorem gives a polynomial dependence on the expansion parameter for the number of available cycle lengths. Theorem 1 of the paper gives a weaker dependence through its spacing guarantee.
--
--   **Formalization Note** The paper writes $\Omega(\alpha^3/\log(1/\alpha))n$. One positive constant $c$ is fixed before $\alpha$, and $\log_2(2/\alpha)$ is the disclosed endpoint-safe reading of its logarithm. The source does not state an $n$ threshold, but $K_2$ is an $\alpha$-expander with no cycle, so the necessary $n_0$ is allowed to depend on $\alpha$ and precedes the choice of $G$.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 3, Theorem 2 (restated p. 13)

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- Friedman–Krivelevich, Theorem 2, p. 3 (restated p. 13). -/
theorem theorem_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), CycleLengthsExp.WellSpread.IsAlphaExpander α G →
        c * (α ^ 3 / Real.logb 2 (2 / α)) * (n : ℝ) ≤
          ((CycleLengthsExp.WellSpread.cycleLengths G).ncard : ℝ) := by sorry

end CycleLengthsExp.ManyLengths
