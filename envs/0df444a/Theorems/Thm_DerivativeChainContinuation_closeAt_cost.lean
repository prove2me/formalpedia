-- Prove2me | Theorems.Thm_DerivativeChainContinuation_closeAt_cost
-- name    : DerivativeChainContinuation.closeAt_cost
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:56:08.869182+00:00
-- url     : https://prove2.me/theorems/58663fa9-436e-4977-966b-17231f4b20b0
-- title:
--   Appending a constant return adds exactly one closing edge
-- statement:
--   Let $r,s\in\mathbb N$ satisfy $r\ge1$ and $s>0$, let $f:\mathbb N\to\mathbb C$, and let $u\in\mathbb C$. Form a path of length $r+s$ by taking $f(0),\ldots,f(r-1)$ and then repeating $u$. Its cost is
--
--   $$L(\operatorname{closeAt}(r,f,u))=L(f|_{\{0,\ldots,r-1\}})+|u-f(r-1)|.$$
--
--   The later repeated entries contribute no additional edges.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ReturnPath.lean#L10-L27

import Mathlib
import Definitions.Def_DerivativeChainContinuation_ReturnPath
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace DerivativeChainContinuation
open DerivativeChainPrivate
open scoped BigOperators





end DerivativeChainContinuation

theorem DerivativeChainContinuation.closeAt_cost (r s : ℕ) (hr : 1 ≤ r) (hs : 0 < s) (f : ℕ → ℂ) (u : ℂ) :
    chainCost (fun i : Fin (r+s) => closeAt r f u i) =
      chainCost (fun i : Fin r => f i)+‖u-f (r-1)‖ := by sorry
