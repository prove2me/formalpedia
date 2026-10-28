-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_static_vanilla_surface_constraints
-- name    : FinancialDerivatives.FD01.static_vanilla_surface_constraints
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:18:46.859452+00:00
-- url     : https://prove2.me/theorems/485c4ae4-16ce-4565-b8e8-3613ff7bd8e2
-- title:
--   Integrated no-arbitrage envelope of a European option surface
-- statement:
--   Integrated no-arbitrage envelope of a European option surface. For one finite nonempty state space and one strictly positive discount factor, the entire strike surface simultaneously satisfies parity, sharp option-price bounds, monotonicity, Lipschitz control, convexity and nonnegative equal-spacing butterflies. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   C(K)-P(K)=S_0-DK,\quad 0\leq C(K)\leq S_0,\quad 0\leq P(K)\leq DK
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. For one finite nonempty state space and one strictly positive discount factor, the entire strike surface simultaneously satisfies parity, sharp option-price bounds, monotonicity, Lipschitz control, convexity and nonnegative equal-spacing butterflies.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_spotValue
import Definitions.Def_fd01_callValue
import Definitions.Def_fd01_putValue

namespace FinancialDerivatives.FD01

theorem static_vanilla_surface_constraints {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (hs : ∀ ω, 0 ≤ s ω) :
  (∀ K : ℝ, 0 ≤ K →
       m.callValue s K - m.putValue s K = m.spotValue s - m.discount * K ∧
       0 ≤ m.callValue s K ∧ m.callValue s K ≤ m.spotValue s ∧
       0 ≤ m.putValue s K ∧ m.putValue s K ≤ m.discount * K ∧
       max (m.spotValue s - m.discount * K) 0 ≤ m.callValue s K ∧
       max (m.discount * K - m.spotValue s) 0 ≤ m.putValue s K) ∧
      (∀ K₁ K₂ : ℝ, 0 ≤ K₁ → K₁ ≤ K₂ →
       0 ≤ m.callValue s K₁ - m.callValue s K₂ ∧
       m.callValue s K₁ - m.callValue s K₂ ≤ m.discount * (K₂ - K₁) ∧
       0 ≤ m.putValue s K₂ - m.putValue s K₁ ∧
       m.putValue s K₂ - m.putValue s K₁ ≤ m.discount * (K₂ - K₁)) ∧
      (∀ K₁ K₂ : ℝ,
       |m.callValue s K₁ - m.callValue s K₂| ≤ m.discount * |K₁ - K₂| ∧
       |m.putValue s K₁ - m.putValue s K₂| ≤ m.discount * |K₁ - K₂|) ∧
      (∀ K₁ K₂ w : ℝ, 0 ≤ w → w ≤ 1 →
       m.callValue s (w * K₁ + (1 - w) * K₂) ≤
           w * m.callValue s K₁ + (1 - w) * m.callValue s K₂ ∧
       m.putValue s (w * K₁ + (1 - w) * K₂) ≤
           w * m.putValue s K₁ + (1 - w) * m.putValue s K₂) ∧
      (∀ K₁ K₂ K₃ : ℝ, 0 ≤ K₁ → K₁ ≤ K₂ → K₂ ≤ K₃ →
       2 * K₂ = K₁ + K₃ →
       0 ≤ m.callValue s K₁ - 2 * m.callValue s K₂ + m.callValue s K₃) := by sorry

end FinancialDerivatives.FD01
