-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finiteEndpointCost_lipschitz
-- name    : DerivativeChainContinuation.finiteEndpointCost_lipschitz
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T16:50:54.868002+00:00
-- url     : https://prove2.me/theorems/20d76dde-6904-4580-9a7d-f8cc6737bc7e
-- title:
--   Finite endpoint extension costs are 1-Lipschitz
-- statement:
--   Let $I$ be a finite nonempty index set, $c_i\in\mathbb R$ prefix costs, and $x_i\in\mathbb C$ endpoints. Define $F(v)=\inf_{i\in I}(c_i+|x_i-v|)$. For all $v,w\in\mathbb C$,
--
--   $$|F(v)-F(w)|\le |v-w|.$$
--
--   The estimate controls variation of optimal transport costs as the terminal point changes.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/EndpointCost.lean#L36-L53

import Mathlib
import Definitions.Def_DerivativeChainContinuation_EndpointCost
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.finiteEndpointCost_lipschitz {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (x : ι → ℂ) (v w : ℂ) :
    |finiteEndpointCost c x v-finiteEndpointCost c x w| ≤ ‖v-w‖ := by sorry
