-- Prove2me | Theorems.Thm_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one
-- name    : Algebra.isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/21f875cb-8d4d-5ebd-9063-939e0cb74874
-- title:
--   Unramifiedness at a horizontal height-one prime from ramification index one
-- statement:
--   Let $L$ be a field of characteristic zero which is the fraction field of a discrete valuation ring $A$, let $F$ and $F'$ be fields that are $L$-algebras and $A$-algebras compatibly, and let $\varphi : F' \to F$ be an $L$-algebra homomorphism whose underlying ring homomorphism is integral. Let $B$ be an integrally closed domain with $A$-algebra and $B$-algebra-on-$F$ structures making $A \to B \to F$ a scalar tower and $F$ the fraction field of $B$, and let $B'$ be a Noetherian integrally closed domain, similarly an $A$-algebra with fraction field $F'$, together with a $B'$-algebra structure on $B$ that is compatible with $A$ and makes $B$ a finite $B'$-module; assume the compatibility $\varphi(\iota_{B'}(x)) = \iota_B(\iota_{B'\to B}(x))$ for all $x \in B'$, where $\iota$ denote the relevant structure maps into $F$ and $F'$. Fix $j_B \in B$ and assume: for every place $w$ of $F$ over $L$ (a proper valuation subring of $F$ containing the image of $L$ whose underlying ring is a principal ideal ring) with $0 \le \operatorname{ord}_w(j_B)$, where $\operatorname{ord}_w$ is minus the logarithm of the $\mathbb{Z}^{m0}$-valued adic valuation of $w$, the ramification index of $w$ along $\varphi$ equals $1$; that index is the least positive $n$ for which some nonzero $f \in F'$ has $\operatorname{ord}_w(\varphi f) = n$, the $F'$-algebra structure on $F$ being the one given by $\varphi$. Let $\varpi \in A$ generate the maximal ideal of $A$, and let $Q$ be a prime ideal of $B$ of height $1$ with the image of $\varpi$ in $B$ not in $Q$. Then $B$ is unramified over $B'$ at $Q$, i.e. the localisation of $B$ at $Q$ is a formally unramified $B'$-algebra.
--
--   This is the local criterion transferring a place-theoretic statement — ramification index one at all places where a chosen function is regular — into commutative-algebra unramifiedness at the horizontal (i.e. not containing the uniformiser of the base discrete valuation ring) height-one primes of a finite extension of integrally closed domains. It is used in the analysis of the integral models of the modular curves $X_1$, where it supplies the unramifiedness of the chart algebras away from the fibre over the residue characteristic, en route to their finiteness and étaleness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (F : Type) [Field F] [Algebra L F] [Algebra A F] [IsScalarTower A L F]
    (F' : Type) [Field F'] [Algebra L F'] [Algebra A F'] [IsScalarTower A L F']
    (φ : F' →ₐ[L] F)
    (B : Type) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Algebra B F] [IsScalarTower A B F]
    [IsFractionRing B F]
    (B' : Type) [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A B'] [Algebra B' F']
    [IsScalarTower A B' F'] [IsFractionRing B' F']
    [Algebra B' B] [IsScalarTower A B' B] [Module.Finite B' B]
    (hι : ∀ x : B', algebraMap B F (algebraMap B' B x) = φ (algebraMap B' F' x))
    (hint : φ.toRingHom.IsIntegral)
    (jB : B)
    (he : ∀ w : AlgebraicCurve.Place L F, 0 ≤ w.ord (algebraMap B F jB) →
      AlgebraicCurve.Place.ramificationIndexAlong φ w = 1)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (Q : Ideal B) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hϖQ : algebraMap A B ϖ ∉ Q) :
    Algebra.IsUnramifiedAt B' Q := by sorry
