-- Prove2me | Theorems.Thm_DerivativeChainContinuation_binomial_geodesic_to_root
-- name    : DerivativeChainContinuation.binomial_geodesic_to_root
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:45:46.125902+00:00
-- url     : https://prove2.me/theorems/70f83f93-1429-4fd6-9272-529ec15c5ca0
-- title:
--   A binomial polynomial has an outward radial derivative chain
-- statement:
--   Let $q,r\in\mathbb N$ with $q\ge2$, let $c,b\in\mathbb C$, and suppose $b^q=-c$. For $p(X)=X^r(X^q+c)$ there is an actual derivative chain $z_0,\ldots,z_{q+r-1}$ such that
--
--   $$z_0=0,\quad z_{q+r-1}=b,\quad |z_{i+1}-z_i|=|z_{i+1}|-|z_i|\quad(0\le i<q+r-1).$$
--
--   The equality makes the chain length telescope to $|b|$. For a finite complex path $z_0,\ldots,z_{N-1}$, write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. An actual derivative chain for a degree-$N$ polynomial $p$ satisfies $p^{(N-i-1)}(z_i)=0$ for every $0\le i<N$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/BinomialGeodesic.lean#L7-L72

import Mathlib
import Definitions.Def_DerivativeChainContinuation_BinomialRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial



end DerivativeChainContinuation

theorem DerivativeChainContinuation.binomial_geodesic_to_root (q r : ℕ) (hq : 2 ≤ q) (c b : ℂ) (hb : b^q= -c) :
    ∃ z : ℕ → ℂ, z 0=0 ∧ z (q+r-1)=b ∧
      (∀ i < q+r, (derivative^[q+r-(i+1)] (binomialPoly q r c)).eval (z i)=0) ∧
      (∀ i < q+r-1, ‖z (i+1)-z i‖ = ‖z (i+1)‖-‖z i‖) := by sorry
