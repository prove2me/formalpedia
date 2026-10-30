-- Prove2me | Theorems.Thm_DerivativeChainContinuation_complexRowHistoryCost_attained
-- name    : DerivativeChainContinuation.complexRowHistoryCost_attained
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:33:23.046935+00:00
-- url     : https://prove2.me/theorems/51a7f5fb-595c-4bff-9dcc-34524b83660c
-- title:
--   Complex row endpoint costs are attained by complete histories
-- statement:
--   For any complex row family $r_k$ with $k+1$ slots and any endpoint $v$ in row $n$, there is one complete row history ending at $v$ whose full consecutive-distance cost equals the recursively defined endpoint cost. Repeated slots and the one-point first row are allowed.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ComplexHistories.lean#L24-L49

import Mathlib
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.complexRowHistoryCost_attained (r : ComplexRootRows) (n : ℕ) (v : ℂ)
    (hv : ∃ j : Fin (n+1), v=r n j) :
    ∃ z : Fin (n+1) → ℂ, IsComplexRowHistory r z ∧ z (Fin.last n)=v ∧
      chainCost z=complexRowHistoryCost r n v := by sorry
