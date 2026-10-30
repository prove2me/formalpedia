-- Prove2me | Theorems.Thm_DerivativeChainContinuation_near_collision_polynomial_chain
-- name    : DerivativeChainContinuation.near_collision_polynomial_chain
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:01:34.960591+00:00
-- url     : https://prove2.me/theorems/8acada45-4a16-4145-bf0f-743bfc25ef46
-- title:
--   Complete actual polynomial chains from local root mass
-- statement:
--   Let $p=\prod_{i=0}^{n}(X-a_i)$ and let $P_{k+1}=D^{n-k}p$. Suppose every root of each proper row $P_{k+1}$ has uniform root mass at least $\alpha_k>0$ in its closed radius-$\rho_k$ ball. Then a complete actual derivative-root chain exists with $$L\le\sum_{k=0}^{n-1}\left(2\rho_k+\frac{G(P_{k+2})-G(P_{k+1})}{\alpha_k}\right).$$ Each Gini dispersion uses the actual root multiset with multiplicity. No supplied coupling, centering or simplicity assumption is required.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/PolynomialNearCollision.lean#L40-L71

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialNearCollision
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem DerivativeChainContinuation.near_collision_polynomial_chain (n : ℕ) (a : Fin (n+1) → ℂ) (ρ α : ℕ → ℝ)
    (ha : ∀ k<n, 0 < α k)
    (hmass : ∀ k<n,∀ x : ℂ,(derivative^[n-k] (fromRoots a)).eval x=0 →
      α k ≤ polynomialLocalMass (derivative^[n-k] (fromRoots a)) x (ρ k)) :
    ∃ z : Fin (n+1) → ℂ, DerivativeChainPrivate.IsChain a z ∧
      chainCost z ≤ ∑ k ∈ Finset.range n, (2*ρ k+
        (polynomialGini (derivative^[n-(k+1)] (fromRoots a))-
          polynomialGini (derivative^[n-k] (fromRoots a)))/α k) := by sorry
