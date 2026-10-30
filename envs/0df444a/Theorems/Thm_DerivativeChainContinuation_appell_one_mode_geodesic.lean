-- Prove2me | Theorems.Thm_DerivativeChainContinuation_appell_one_mode_geodesic
-- name    : DerivativeChainContinuation.appell_one_mode_geodesic
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:48:08.099176+00:00
-- url     : https://prove2.me/theorems/77441952-2970-49f7-a180-bd3aeb50710f
-- title:
--   One-mode Appell rows admit a geodesic to a chosen endpoint
-- statement:
--   Let $2\le q\le M$, let $c:\mathbb N\to\mathbb C$ satisfy $c_0=1$ and $c_j=0$ for $j\le M$ outside $\{0,q\}$, and let $b^q=-\binom Mq c_q$. There are points $z_0,\ldots,z_{M-1}$ with
--
--   $$z_0=0,\quad z_{M-1}=b,\quad A_{i+1}(z_i)=0,\quad |z_{i+1}-z_i|=|z_{i+1}|-|z_i|.$$
--
--   The last two assertions apply to $i<M$ and $i<M-1$, respectively. For $c:\mathbb N\to\mathbb C$, write $A_m(X)=\sum_{j=0}^m\binom mj c_jX^{m-j}$ and $A_{m,u}(X)=A_m(X-u)$. This supplies a compatible sparse prefix, not merely independent roots.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AppellPrefix.lean#L30-L49

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellRows
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

theorem DerivativeChainContinuation.appell_one_mode_geodesic (M q : ℕ) (hq : 2 ≤ q) (hqM : q ≤ M)
    (c : ℕ → ℂ) (hc0 : c 0=1)
    (hs : ∀ j ≤ M, j ≠ 0 → j ≠ q → c j=0)
    (b : ℂ) (hb : b^q= -((M.choose q:ℂ)*c q)) :
    ∃ z : ℕ → ℂ, z 0=0 ∧ z (M-1)=b ∧
      (∀ i < M, (appellRow (i+1) c).eval (z i)=0) ∧
      (∀ i < M-1, ‖z (i+1)-z i‖ = ‖z (i+1)‖-‖z i‖) := by sorry
