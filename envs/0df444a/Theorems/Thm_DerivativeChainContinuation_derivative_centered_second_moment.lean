-- Prove2me | Theorems.Thm_DerivativeChainContinuation_derivative_centered_second_moment
-- name    : DerivativeChainContinuation.derivative_centered_second_moment
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:09:21.989716+00:00
-- url     : https://prove2.me/theorems/1dd02e16-1899-42e9-bcfb-2098fd94dcab
-- title:
--   Second holomorphic moment under differentiation
-- statement:
--   Let $p$ be monic of degree $n+3$ with zero root sum, and let $q$ be its monic normalized derivative. Counting root multiplicity, $$ (n+3)\sum_{q(w)=0}w^2=(n+1)\sum_{p(z)=0}z^2.$$ This is an identity of complex second moments.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/PolynomialMoments.lean#L39-L54

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.derivative_centered_second_moment (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hdeg : p.natDegree = n+3) (hcenter : p.roots.sum = 0) :
    (n+3 : ℂ) * ((monicDerivative p).roots.map fun z => z^2).sum =
      (n+1 : ℂ) * (p.roots.map fun z => z^2).sum := by sorry
