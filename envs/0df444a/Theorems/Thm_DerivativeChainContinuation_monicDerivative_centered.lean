-- Prove2me | Theorems.Thm_DerivativeChainContinuation_monicDerivative_centered
-- name    : DerivativeChainContinuation.monicDerivative_centered
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:07:33.262002+00:00
-- url     : https://prove2.me/theorems/dbd60318-2670-4055-9b3a-ef27b717b27e
-- title:
--   Differentiation preserves a zero root sum
-- statement:
--   Let $p$ be a monic complex polynomial of degree $n+3$, where $n\ge0$, whose roots sum to zero with multiplicity. Its monic normalized derivative also has root sum zero.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/PolynomialMoments.lean#L20-L37

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.monicDerivative_centered (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hdeg : p.natDegree = n+3) (hcenter : p.roots.sum = 0) :
    (monicDerivative p).roots.sum = 0 := by sorry
