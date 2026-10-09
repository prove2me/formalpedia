-- Prove2me | Theorems.Thm_CycleLengthsExp_WellSpread_theorem_1
-- name    : CycleLengthsExp.WellSpread.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:26.635313+00:00
-- url     : https://prove2.me/theorems/8ed8d257-9d2c-4b3c-8309-27cf11f6b588
-- title:
--   Theorem 1 — an α-expander has a cycle with length in [ℓ, ℓ+A] for every integer ℓ ∈ [a₁ log n, a₂ n], A, a₁ = O(1/α), a₂ = 2^{−O(log(1/α)/α)}
-- statement:
--   For every $0<\alpha\le1$ there exist positive constants
--
--   $$A=O\!\left(\frac1\alpha\right),\qquad a_1=O\!\left(\frac1\alpha\right),\qquad a_2=2^{-O\left(\frac{\log(1/\alpha)}{\alpha}\right)}$$
--
--   such that, for all large enough $n$, every $\alpha$-expander $G$ on $n$ vertices contains, for every integer $\ell\in[a_1\log_2 n,\ a_2n]$, a cycle whose length $L$ satisfies $\ell\le L\le\ell+A$.
--
--   The cycle lengths of an $\alpha$-expander are thus well spread: from logarithmic up to linear length, every window of length $O(1/\alpha)$ contains one. The order $1/\alpha$ of the window is optimal (subdivided bounded-degree expanders have all cycle lengths divisible by $\Theta(1/\alpha)$).
--
--   **Formalization Note.** The $O(\cdot)$ notation is encoded with one absolute constant $K>0$ quantified before $\alpha$: $A\le K/\alpha$, $a_1\le K/\alpha$ and $a_2\ge 2^{-K\log_2(2/\alpha)/\alpha}$. Inside the $O$, $\log(1/\alpha)$ is read as $\log_2(2/\alpha)=1+\log_2(1/\alpha)$, which agrees with it up to a constant factor for $\alpha\le1/2$ and avoids the degenerate value $0$ at $\alpha=1$. "For large enough $n$" is a threshold $n_0$ depending on $\alpha$ (and the constants) only. A cycle is a closed walk of length at least $3$ without repeated vertices.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 3, Theorem 1 (restated p. 9, proof pp. 9–12)

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

namespace CycleLengthsExp.WellSpread

theorem theorem_1 :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∃ A a₁ a₂ : ℝ, 0 < A ∧ A ≤ K / α ∧ 0 < a₁ ∧ a₁ ≤ K / α ∧ 0 < a₂ ∧
        (2 : ℝ) ^ (-(K * Real.logb 2 (2 / α) / α)) ≤ a₂ ∧
        ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), IsAlphaExpander α G →
          ∀ ℓ : ℕ, a₁ * Real.logb 2 n ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ a₂ * n →
            ∃ L ∈ cycleLengths G, ℓ ≤ L ∧ (L : ℝ) ≤ ℓ + A := by sorry

end CycleLengthsExp.WellSpread
