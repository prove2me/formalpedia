-- Prove2me | Theorems.Thm_FMLPricing_BranchBound_proposition_2
-- name    : FMLPricing.BranchBound.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:40.633851+00:00
-- url     : https://prove2.me/theorems/fa911b4d-62a4-402a-a292-1ef1a3dd1c04
-- title:
--   Proposition 2, p. 12 — a (1 − ε)-optimal x′ ∈ X yields (1 − ε)-optimal prices p′ = −b⁻¹ log z′
-- statement:
--   Let $x' \in X$, let $z' \in [\underline z, \bar z]$ be a maximizer of $\texttt{cnstr-rev}(x')$, and let $\varepsilon > 0$. Suppose
--   $$
--   \pi(x') \ge (1 - \varepsilon) \max_{x \in X} \pi(x).
--   $$
--   Then the price vector $p' = (-b_1^{-1} \log z'_1, \dots, -b_n^{-1} \log z'_n)$ lies in $[\underline p, \bar p]$, and
--   $$
--   \Pi(p') \ge (1 - \varepsilon) \max_{p \in [\underline p, \bar p]} \Pi(p).
--   $$
--
--   A $(1-\varepsilon)$-approximation in the no-purchase probabilities therefore converts into a $(1-\varepsilon)$-approximation in prices. Algorithm 1 relies on this conversion for its output.
--
--   **Formalization Note** Each maximum is read at a maximizer: the hypothesis is required for every maximizer $x_0$ of $\pi$ on $X$, and the conclusion is asserted for every maximizer $p_0$ of $\Pi$ on $[\underline p, \bar p]$. Equation (5) shows that both exist. No restriction $\varepsilon < 1$ is imposed.
-- source:
--   van de Geer & den Boer, Price Optimization Under the Finite-Mixture Logit Model, SSRN 3235432 (version of August 26, 2021), p. 12, Proposition 2 (proof pp. 33–34)

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model

namespace FMLPricing.BranchBound

/-- Proposition 2, p. 12: a `(1 − ε)`-optimal `x' ∈ X` and a maximizer `z'` of
`cnstr-rev(x')` give prices `p' = (−b_j⁻¹ log z'_j)_j ∈ [p̲, p̄]` that are `(1 − ε)`-optimal
on `[p̲, p̄]`. The maxima are read at maximizers. -/
theorem proposition_2 {m n : ℕ} (I : FML m n) (hI : Standing I)
    (x' : Fin m → ℝ) (hx' : x' ∈ Xset I) (z' : Fin n → ℝ) (hz' : IsCnstrMax I x' z')
    (ε : ℝ) (hε : 0 < ε)
    (happrox : ∀ x₀ ∈ Xset I, (∀ x ∈ Xset I, piX I x ≤ piX I x₀) →
      (1 - ε) * piX I x₀ ≤ piX I x') :
    priceOf I z' ∈ priceBox I ∧
      ∀ p₀ ∈ priceBox I, (∀ p ∈ priceBox I, Pi I p ≤ Pi I p₀) →
        (1 - ε) * Pi I p₀ ≤ Pi I (priceOf I z') := by sorry

end FMLPricing.BranchBound
