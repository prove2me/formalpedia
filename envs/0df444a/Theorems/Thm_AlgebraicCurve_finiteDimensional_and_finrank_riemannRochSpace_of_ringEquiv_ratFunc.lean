-- Prove2me | Theorems.Thm_AlgebraicCurve_finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc
-- name    : AlgebraicCurve.finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/a26cfdcc-1bde-557f-9a0b-a139f55e1594
-- title:
--   Riemann–Roch in genus 0: dim_k L(E)=max(deg E+1,0)
-- statement:
--   Let $k$ be an algebraically closed field and let $F$ be a field equipped with a $k$-algebra structure. Assume given a ring isomorphism $e : k(X) \to F$ from the field of rational functions over $k$ such that $e$ carries the structure map $k \to k(X)$ to the structure map $k \to F$, so that $e$ is an isomorphism of $k$-algebras. Let $E$ be a divisor of $F$ over $k$, that is, a finitely supported function from the places of $F/k$ to $\mathbb{Z}$, a place being a valuation subring of $F$ containing the image of $k$, distinct from $F$ itself, and a principal ideal ring. Then the associated Riemann–Roch space — the $k$-submodule of those $f \in F$ with $v(f) \le \exp(E(v))$ for every place $v$, where $v$ denotes the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of the valuation subring of $v$ — is a finite-dimensional $k$-vector space, and its $k$-dimension equals the natural number $\max(\deg E + 1, 0)$, where $\deg E = \sum_v E(v)\,\deg v$ is the degree of $E$. No positivity assumption is made on $E$: for $\deg E < -1$ the asserted dimension is $0$.
--
--   This is the Riemann–Roch theorem for the projective line, in the form valid for divisors of arbitrary sign, stated for any function field $k$-isomorphic to $k(X)$ over an algebraically closed field. It is used to compute the cohomology of line bundles on a rational curve model and to produce functions in Riemann–Roch spaces with prescribed order at a place, in the analysis of specialisations on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (e : RatFunc k ≃+* F) (he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k F c)
    (E : Divisor k F) :
    FiniteDimensional k ↥(riemannRochSpace E) ∧
      Module.finrank k ↥(riemannRochSpace E) = (E.degree + 1).toNat := by sorry
