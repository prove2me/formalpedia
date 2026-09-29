-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
-- name    : AlgebraicCurve.Place.ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/96161970-8f48-5351-80d8-ea47fb63f489
-- title:
--   Kummer covers are totally ramified when ord u is prime to n
-- statement:
--   Let $k$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $k$, and assume $F'$ has principal divisors over $k$, i.e. every nonzero $f \in F'$ admits a finitely supported integer-valued function on the places of $F'/k$ whose value at each place $v$ is $v.\mathrm{ord}(f)$ and whose degree is $0$. Let $\varphi \colon F \to F'$ be a $k$-algebra homomorphism whose underlying ring homomorphism is integral; equip $F'$ with the $F$-algebra structure given by $\varphi$, and assume that with respect to it $F'$ is a finite $F$-module, is separable over $F$, and has $\operatorname{finrank}_F F' = n$ for a natural number $n$. Let $c \in F'$ and $u \in F$ satisfy $\varphi(u) = c^{n}$, and let $P$ be a place of $F'/k$, that is, a proper valuation subring of $F'$ containing the image of $k$ and which is a principal ideal ring. Suppose $\mathrm{ord}$ of $u$ at the restricted place $P|_F$ (the preimage of $P$'s valuation subring under $\varphi$) is coprime to $n$ in $\mathbb{Z}$. Then the ramification index of $P$ over $F$ — the infimum of the positive integers of the form $P.\mathrm{ord}(\varphi f)$ for nonzero $f \in F$ — equals $n$.
--
--   This is the standard criterion for a degree-$n$ Kummer-type cover $c^{n} = \varphi(u)$ to be totally ramified at a place where the order of $u$ downstairs is prime to $n$. It is used in the genus computation for such covers and in the enumeration of places of the Drinfeld curve function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.ramificationIndexAlong_eq_of_pow_eq_of_isCoprime_ord
    {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [AlgebraicCurve.HasPrincipalDivisors k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong k φ) (hsep : AlgebraicCurve.SeparableAlong k φ)
    (n : ℕ) (hdeg : AlgebraicCurve.finrankAlong k φ = n)
    (c : F') (u : F) (hu : φ u = c ^ n)
    (P : AlgebraicCurve.Place k F')
    (hcop : IsCoprime ((P.restrictAlong φ hφ).ord u) (n : ℤ)) :
    P.ramificationIndexAlong φ = n := by sorry
