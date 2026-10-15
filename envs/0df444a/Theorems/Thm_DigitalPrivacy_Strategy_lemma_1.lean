-- Prove2me | Theorems.Thm_DigitalPrivacy_Strategy_lemma_1
-- name    : DigitalPrivacy.Strategy.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:40.391884+00:00
-- url     : https://prove2.me/theorems/44e54f88-acfe-4bb4-b690-63de8fbca854
-- title:
--   Lemma 1, p. 29 — for fixed data collection ξ, the optimal protection is max{C_h(ξ), 0}
-- statement:
--   Let $0 \le \beta < 1$, $0 \le \rho < 1$, $\psi > 0$ and $0 \le P \le 1$, and fix a data collection level $\xi \in [0, 1]$. Let $\Pi(\xi, C) = (1-P)\bar a^*(\xi, C) + P\xi\bar a^*(\xi, C) - \psi C$ be the business's profit and
--   $$C_h(\xi) = \frac{1}{1-\beta}\Big(-\xi^2 + \xi\sqrt{\tfrac1\psi(1+\rho\xi)(1-P+P\xi)}\Big).$$
--   Then $C^*(\xi) = \max\{C_h(\xi), 0\}$ is the unique maximizer of $C \mapsto \Pi(\xi, C)$ over $C \ge 0$: for every $C \ge 0$,
--   $$\Pi(\xi, C) \le \Pi\big(\xi, \max\{C_h(\xi), 0\}\big),$$
--   with equality only if $C = \max\{C_h(\xi), 0\}$.
--
--   This is the business's best protection response to a given collection level; Theorem 1's $C^\star$ is this response evaluated at $\xi^\star$.
--
--   **Formalization Note** The paper allows $\psi \ge 0$; the statement assumes $\psi > 0$, since $C_h$ contains $1/\psi$ and for $\psi = 0$, $\xi > 0$ the profit increases in $C$ without bound being attained. Uniqueness is the reading of "the business sets". Footnote 29 (when $C_h(\xi) > 0$) is not part of the statement.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), p. 29, Lemma 1; proof Online App. B

import Mathlib
import Definitions.Def_DigitalPrivacy_Strategy_Setting

namespace DigitalPrivacy.Strategy

/-- Lemma 1, p. 29: for a fixed data collection level `ξ ∈ [0, 1]`, the protection level
`max{C_h(ξ), 0}` is the unique maximizer of `C ↦ Π(ξ, C)` over `C ≥ 0`. -/
theorem lemma_1 (β ρ ψ P ξ : ℝ) (hB : Basic β ρ ψ P) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ max (Ch β ρ ψ P ξ) 0 ∧
    ∀ C : ℝ, 0 ≤ C →
      profit β ρ ψ P ξ C ≤ profit β ρ ψ P ξ (max (Ch β ρ ψ P ξ) 0) ∧
      (profit β ρ ψ P ξ C = profit β ρ ψ P ξ (max (Ch β ρ ψ P ξ) 0) →
        C = max (Ch β ρ ψ P ξ) 0) := by sorry

end DigitalPrivacy.Strategy
