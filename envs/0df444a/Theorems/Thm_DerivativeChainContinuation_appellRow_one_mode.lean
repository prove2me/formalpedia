-- Prove2me | Theorems.Thm_DerivativeChainContinuation_appellRow_one_mode
-- name    : DerivativeChainContinuation.appellRow_one_mode
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:36:41.887195+00:00
-- url     : https://prove2.me/theorems/4124b1ae-d59b-4bff-926e-f7935d13af84
-- title:
--   A one-mode Appell row is a binomial polynomial
-- statement:
--   Let $M,q\in\mathbb N$ satisfy $0<q\le M$. Let $c:\mathbb N\to\mathbb C$ satisfy $c_0=1$ and $c_j=0$ for $0\le j\le M$ outside $\{0,q\}$. Then
--
--   $$A_M(X)=X^{M-q}\left(X^q+\binom Mq c_q\right).$$
--
--   For $c:\mathbb N\to\mathbb C$, write $A_m(X)=\sum_{j=0}^m\binom mj c_jX^{m-j}$ and $A_{m,u}(X)=A_m(X-u)$. This identifies the initial sparse row used by the geodesic construction.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AppellPrefix.lean#L8-L28

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Definitions.Def_DerivativeChainContinuation_BinomialRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial





end DerivativeChainContinuation

theorem DerivativeChainContinuation.appellRow_one_mode (M q : ℕ) (hq : 0 < q) (hqM : q ≤ M)
    (c : ℕ → ℂ) (hc0 : c 0=1)
    (hs : ∀ j ≤ M, j ≠ 0 → j ≠ q → c j=0) :
    appellRow M c = binomialPoly q (M-q) ((M.choose q:ℂ)*c q) := by sorry
