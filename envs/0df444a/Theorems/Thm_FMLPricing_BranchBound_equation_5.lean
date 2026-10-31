-- Prove2me | Theorems.Thm_FMLPricing_BranchBound_equation_5
-- name    : FMLPricing.BranchBound.equation_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:44.74915+00:00
-- url     : https://prove2.me/theorems/6e0d4682-aed6-4848-b055-cedc2a55879d
-- title:
--   Equation (5), p. 12 — the maximum of π over X equals the maximum of Π over [p̲, p̄]
-- statement:
--   Let $\pi(x)$ be the optimal value of $\texttt{cnstr-rev}(x)$ and $X = \{q_0(p) : p \in [\underline p, \bar p]\}$. Both maxima below are attained, and
--   $$
--   \max_{x \in X} \pi(x) = \max_{p \in [\underline p, \bar p]} \Pi(p).
--   $$
--
--   This identity turns revenue maximization over prices into maximization of $\pi$ over the $m$-dimensional set of no-purchase probabilities.
--
--   **Formalization Note** Stated as: there are $x_0 \in X$ and $p_0 \in [\underline p, \bar p]$ such that $\pi(x_0)$ is the greatest value of $\pi$ on $X$, $\Pi(p_0)$ is the greatest value of $\Pi$ on $[\underline p, \bar p]$, and $\pi(x_0) = \Pi(p_0)$.
-- source:
--   van de Geer & den Boer, Price Optimization Under the Finite-Mixture Logit Model, SSRN 3235432 (version of August 26, 2021), p. 12, Equation (5)

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model

namespace FMLPricing.BranchBound

/-- Equation (5), p. 12: `max_{x ∈ X} π(x) = max_{p ∈ [p̲, p̄]} Π(p)`, both maxima attained. -/
theorem equation_5 {m n : ℕ} (I : FML m n) (hI : Standing I) :
    ∃ x₀ ∈ Xset I, ∃ p₀ ∈ priceBox I,
      IsGreatest (piX I '' Xset I) (piX I x₀) ∧ IsGreatest (Pi I '' priceBox I) (Pi I p₀) ∧
        piX I x₀ = Pi I p₀ := by sorry

end FMLPricing.BranchBound
