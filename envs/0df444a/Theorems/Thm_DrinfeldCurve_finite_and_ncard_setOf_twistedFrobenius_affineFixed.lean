-- Prove2me | Theorems.Thm_DrinfeldCurve_finite_and_ncard_setOf_twistedFrobenius_affineFixed
-- name    : DrinfeldCurve.finite_and_ncard_setOf_twistedFrobenius_affineFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/93360c3d-6206-5189-8daa-becd2c28fef6
-- title:
--   Fixed affine points of twisted q²-Frobenius on the Drinfeld curve
-- statement:
--   Let $q$ be a prime, let $K$ be an algebraically closed field equipped with an algebra structure over the field $\mathbb{F}_{q^2}$ (Mathlib's `GaloisField q 2`), and let $\eta$ be an element of the group of $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$, that is, a unit of $\mathbb{F}_{q^2}$ with $\eta^{q+1}=1$, viewed in $K$ through the structure map $\mathbb{F}_{q^2}\to K$. Consider the set $S_\eta$ of pairs $(a,b)\in K\times K$ satisfying the three equations $$a b^{q} - a^{q} b = 1,\qquad \eta\, a^{q^{2}} = a,\qquad \eta\, b^{q^{2}} = b,$$ the affine points of the Drinfeld curve $xy^{q}-x^{q}y=1$ over $K$ fixed by the composite of the $q^{2}$-power Frobenius with multiplication by $\eta$. The theorem asserts three things simultaneously: first, $S_\eta$ is finite; second, if $\eta=-1$ as an element of $\mathbb{F}_{q^2}$ then the cardinality of $S_\eta$ (as a `Set.ncard`) equals $q^{3}-q$; and third, if $\eta\neq-1$ then $S_\eta$ is empty.
--
--   This is the elementary finite-field count of the affine $\eta$-twisted Frobenius-fixed points of the Drinfeld (Deligne–Lusztig) curve attached to $\mathrm{SL}_2(\mathbb{F}_q)$: combined with the places at infinity it yields the fixed-place numbers of the twisted curve, which are maximal over $\mathbb{F}_{q^2}$ precisely for $\eta=-1$. It is used by [`DrinfeldCurve.natCard_place_restrictAlong_eq_neg_one_smul`](thm.html#DrinfeldCurve.natCard_place_restrictAlong_eq_neg_one_smul) and [`DrinfeldCurve.natCard_restrictAlong_eq_hFunctionFieldAction_one_smul_of_ne_neg_one`](thm.html#DrinfeldCurve.natCard_restrictAlong_eq_hFunctionFieldAction_one_smul_of_ne_neg_one), which record the corresponding counts of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_finite_and_ncard_setOf_twistedFrobenius_affineFixed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace DrinfeldCurve

theorem finite_and_ncard_setOf_twistedFrobenius_affineFixed
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [Algebra (GaloisField q 2) K] [IsAlgClosed K]
    (η : rootsOfUnity (q + 1) (GaloisField q 2)) :
    {p : K × K | p.1 * p.2 ^ q - p.1 ^ q * p.2 = 1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.1 ^ q ^ 2 = p.1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.2 ^ q ^ 2 = p.2}.Finite ∧
    (((η : (GaloisField q 2)ˣ) : GaloisField q 2) = -1 →
      {p : K × K | p.1 * p.2 ^ q - p.1 ^ q * p.2 = 1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.1 ^ q ^ 2 = p.1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.2 ^ q ^ 2 = p.2}.ncard = q ^ 3 - q) ∧
    (((η : (GaloisField q 2)ˣ) : GaloisField q 2) ≠ -1 →
      {p : K × K | p.1 * p.2 ^ q - p.1 ^ q * p.2 = 1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.1 ^ q ^ 2 = p.1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.2 ^ q ^ 2 = p.2} = ∅) := by sorry
