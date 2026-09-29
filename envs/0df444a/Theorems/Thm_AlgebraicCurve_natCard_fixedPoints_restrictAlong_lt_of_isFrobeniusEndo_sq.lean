-- Prove2me | Theorems.Thm_AlgebraicCurve_natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq
-- name    : AlgebraicCurve.natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/131d4f6f-f3ff-594b-9bf4-7a354643bb9d
-- title:
--   Bombieri's bound on fixed places of a twisted Frobenius
-- statement:
--   Let $K$ be an algebraically closed field and $E$ a field equipped with a $K$-algebra structure which is a curve over $K$ in the sense of the project predicate [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in E$ has a divisor $D$ with $D(v) = \mathrm{ord}_v(f)$ at every place $v$ of $E/K$ and $\deg D = 0$; the residue field of every place is finite-dimensional over $K$; and $\Omega[E/K]$ is free of rank $1$ over $E$. Here a place of $E/K$ is a valuation subring of $E$ containing the image of $K$, distinct from $E$ itself, and a principal ideal ring. Assume $E$ is generated over $K$ by a finite subset, i.e. there is a finite $s \subseteq E$ with $K(s) = E$ as intermediate fields. Let $q$ be a natural number with $(g+1)^2 < q$, where $g = \mathrm{genusFF}(K,E)$ is the $K$-dimension of $H^1$ of the zero divisor. Let $\psi : E \to E$ be a $K$-algebra homomorphism such that $E$ is integral over $\psi(E)$, and suppose $\psi$ satisfies `IsFrobeniusEndo (q^2)`: every $x \in E$ is of the form $x^{q^2} = \psi(y)$ for some $y$, and $\psi(y)$ is a $q^2$-th power for every $y$; that is, the image of $\psi$ is exactly the subfield $E^{q^2}$. Let $\psi^*$ denote the induced self-map of the set of places of $E/K$, sending $w$ to the place whose valuation subring is the preimage of that of $w$ under $\psi$. Then the set of fixed points of $\psi^*$ is finite and its cardinality is strictly less than $q^2 + 1 + (2g+1)q$.
--
--   This is Bombieri's elementary Riemann–Roch upper bound for the number of rational places, in geometric form for a twisted Frobenius endomorphism: the places fixed by $\psi^*$ play the role of the degree-one places, and over $\overline{\mathbb F}_{q^2}$ with $\psi$ the relative Frobenius the bound is the classical one. It feeds the counting estimate [`AlgebraicCurve.exists_sub_le_sum_divisors_mul_card_places`](thm.html#AlgebraicCurve.exists_sub_le_sum_divisors_mul_card_places), on the way to the Riemann hypothesis for curves over finite fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq
    (K E : Type*) [Field K] [IsAlgClosed K] [Field E] [Algebra K E]
    [AlgebraicCurve.IsCurveOver K E]
    (hfg : ∃ s : Finset E, IntermediateField.adjoin K (s : Set E) = ⊤)
    (q : ℕ) (hq : (AlgebraicCurve.genusFF K E + 1) ^ 2 < q)
    (ψ : E →ₐ[K] E) (hψi : ψ.toRingHom.IsIntegral)
    (hψ : AlgebraicCurve.IsFrobeniusEndo (q ^ 2) ψ) :
    (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong ψ hψi)).Finite ∧
      Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong ψ hψi)) <
        q ^ 2 + 1 + (2 * AlgebraicCurve.genusFF K E + 1) * q := by sorry
