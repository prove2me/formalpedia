-- Prove2me | Theorems.Thm_AlgebraicCurve_isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card
-- name    : AlgebraicCurve.isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/33c3cadb-aa6c-51eb-bf68-6a2e1efb1c7d
-- title:
--   Relative q-Frobenius: image F^q, bijective on places, inertia degree 1
-- statement:
--   Let $k$ be a finite field, $K$ an algebraically closed field, and $F_0$, $F$ fields, with $F_0$ a $k$-algebra, $F$ both a $K$-algebra and an $F_0$-algebra, and suppose $F$ is a curve over $K$ in the sense of the project: every nonzero $f \in F$ has a degree-zero divisor whose value at each place is $\operatorname{ord}_v f$, each place of $F/K$ (a valuation subring of $F$ containing the image of $K$, distinct from $F$, and a principal ideal ring) has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Assume $F$ is generated as a field over $K$ by the image of the structure map $F_0 \to F$, i.e. the intermediate field $K(\operatorname{im}(F_0 \to F))$ is all of $F$. Let $\varphi : F \to F$ be a $K$-algebra endomorphism which is integral as a ring homomorphism and satisfies $\varphi(x) = x^q$ for every $x$ in the image of $F_0$, where $q = \#k$. Then: (i) $\varphi$ is a Frobenius endomorphism of exponent $q$, i.e. every $q$-th power in $F$ lies in the image of $\varphi$ and every value of $\varphi$ is a $q$-th power; (ii) the map sending a place $w$ of $F/K$ to the pullback of its valuation subring along $\varphi$ is a bijection on the places of $F/K$; and (iii) for every place $w$, the residue field of $w$ has degree $1$ over the residue field of this pullback.
--
--   This is the standard description of the relative $q$-Frobenius of a curve over a finite field after base change to an algebraically closed field: its image is the subfield of $q$-th powers, it is a bijection on closed points, and it is purely inseparable of inertia degree one at every point. It is used to produce the semilinear identification of the Frobenius action on a curve model with the action on places, and in the computation of traces of Frobenius on Drinfeld curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FrobeniusEndo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [AlgebraicCurve.IsCurveOver K F]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    AlgebraicCurve.IsFrobeniusEndo (Nat.card k) φ ∧
      Function.Bijective (AlgebraicCurve.Place.restrictAlong φ hφi) ∧
      ∀ w : AlgebraicCurve.Place K F, AlgebraicCurve.Place.inertiaDegAlong φ hφi w = 1 := by sorry
