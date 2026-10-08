-- Prove2me | Theorems.Thm_BellmanDP_ExistUnique_type_three_exists_unique
-- name    : BellmanDP.ExistUnique.type_three_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T15:45:54.579517+00:00
-- url     : https://prove2.me/theorems/ae7fc4cb-68fc-4e53-b6ab-e599c87f0b71
-- title:
--   Chapter IV, Theorem 5 — the equation of the third type has a unique bounded solution
-- statement:
--   Let $\Delta$ be the probability simplex of distributions $p = (p_0, \dots, p_n)$, let $x_k$ be its vertices, and let $T_1, \dots, T_M$ ($M \ge 1$) map $\Delta$ into itself, $T_l p = (p_{0l}, \dots, p_{nl})$ with $p_{0l} \ne 1$. Suppose that for each $l$ and all $p \in \Delta$
--   $$\sum_{k=1}^{n} p_{kl} \le c_1, \qquad 0 < c_1 < 1.$$
--   Then the equation
--   $$f(p) = \min\Big[\,1 + \sum_{k=0}^{n} p_k f(x_k),\ \min_{l}\big[1 + f(T_l p)\big]\Big] \quad (p \ne x_0), \qquad f(x_0) = 0,$$
--   has a bounded solution on $\Delta$, any two bounded solutions agree on $\Delta$, and this solution is positive at every $p \ne x_0$.
--
--   The equation describes the minimal expected time to drive a system into state $0$ with certainty, by observing its state or applying one of $M$ randomizing operations. It is neither of Type One nor of Type Two, and its uniqueness does not follow from a contraction argument.
--
--   **Formalization Note** Distributions are functions `Fin (n+1) → ℝ`. Solutions and uniqueness are taken on the simplex. At $n = 0$ the hypotheses cannot be met: $T_l p$ would have to be $x_0$, which $p_{0l} \ne 1$ excludes. The book has the same corner.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IV, § 8, Eqs. (8.1)-(8.2), p. 125, and Theorem 5, p. 126

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_TypeThree

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 8, Theorem 5, p. 126. If for each transformation
`T_l` and all `p`, `Σ_{k=1}^n p_{kl} ≤ c₁` with `0 < c₁ < 1`, then equation (8.1) has a unique
bounded solution on the simplex, and this solution is positive for `p ≠ x₀`. -/
theorem type_three_exists_unique (n M : ℕ)
    (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (c₁ : ℝ)
    (hT : TypeThreeHyp n M Tr c₁) :
    ∃ f : (Fin (n + 1) → ℝ) → ℝ,
      (BoundedOnSimplex n f ∧ SolvesTypeThree n M Tr f) ∧
      (∀ g : (Fin (n + 1) → ℝ) → ℝ, BoundedOnSimplex n g → SolvesTypeThree n M Tr g →
        ∀ p ∈ simplex n, g p = f p) ∧
      (∀ p ∈ simplex n, p ≠ vertex n 0 → 0 < f p) := by sorry

end BellmanDP.ExistUnique
