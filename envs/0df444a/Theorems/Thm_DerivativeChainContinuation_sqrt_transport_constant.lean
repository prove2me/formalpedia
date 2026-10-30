-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sqrt_transport_constant
-- name    : DerivativeChainContinuation.sqrt_transport_constant
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:08:58.492287+00:00
-- url     : https://prove2.me/theorems/65a1ca7c-402b-400b-9881-caeeea0b079c
-- title:
--   Square-root estimate for the transport constant
-- statement:
--   For every real $x\ge0$,
--
--   $$\sqrt{x+2}+4\sqrt{x+1}-4\sqrt2\le5\sqrt x.$$
--
--   This elementary estimate closes the telescoping transport-potential argument with the explicit constant $5$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/TransportMean.lean#L8-L20

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.sqrt_transport_constant (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (x+2)+4*Real.sqrt (x+1)-4*Real.sqrt 2 ≤ 5*Real.sqrt x := by sorry
