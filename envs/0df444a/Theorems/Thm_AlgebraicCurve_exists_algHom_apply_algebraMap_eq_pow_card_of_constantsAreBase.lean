-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_algHom_apply_algebraMap_eq_pow_card_of_constantsAreBase
-- name    : AlgebraicCurve.exists_algHom_apply_algebraMap_eq_pow_card_of_constantsAreBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/d76885a7-add2-5b54-8ccc-aab5114f30b3
-- title:
--   Constant-field Frobenius extends to a K-endomorphism of F
-- statement:
--   Let $k$ be a finite field, and let $K$, $F_0$, $F$ be fields with $k$-algebra structures on $K$, $F_0$ and $F$, an $F_0$-algebra and a $K$-algebra structure on $F$, the two towers $k \to K \to F$ and $k \to F_0 \to F$ being compatible with the $k$-algebra structure on $F$. Assume $F_0$ is a curve over $k$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F_0$ has a divisor $D$ (a finitely supported integral function on the places of $F_0/k$, a place being a valuation subring of $F_0$ containing the image of $k$, different from $F_0$ and a principal ideal ring) with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ and $\deg D = 0$, every residue field of a place is finite-dimensional over $k$, and $\Omega_{F_0/k}$ is free of rank $1$ over $F_0$; assume furthermore that $F_0$ is essentially of finite type over $k$ and that $K$ is algebraic over $k$. Assume [`AlgebraicCurve.ConstantsAreBase k F₀`](def/AlgebraicCurve_AdelicIndex.html#L45), i.e. the Riemann–Roch space of the zero divisor of $F_0/k$ coincides with the image of $k$ in $F_0$, and assume that $F$ is generated as an $F_0$-algebra by the image of $K$, i.e. $\mathrm{adjoin}_{F_0}(\operatorname{range}(K \to F)) = \top$. Then there exists a $K$-algebra homomorphism $\varphi : F \to F$ such that $\varphi(x) = x^{\,\#k}$ for every $x \in F_0$ (read through $F_0 \to F$).
--
--   This is the statement that, for a function field $F_0$ over a finite field $k$ whose constants are exactly $k$, the $\#k$-power Frobenius of $F_0$ extends to an endomorphism of the constant-field extension $F = F_0 \cdot K$ that is the identity on $K$. It is used in the computation of the order of the prime torsion of $\mathrm{Pic}^0$ in terms of the genus, via [`AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_two_mul_genusFF_of_forall_pow_eq_self`](thm.html#AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_two_mul_genusFF_of_forall_pow_eq_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_algHom_apply_algebraMap_eq_pow_card_of_constantsAreBase.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.exists_algHom_apply_algebraMap_eq_pow_card_of_constantsAreBase
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [Field F₀] [Field F]
    [Algebra k K] [Algebra k F₀] [Algebra F₀ F] [Algebra K F] [Algebra k F]
    [IsScalarTower k K F] [IsScalarTower k F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [Algebra.EssFiniteType k F₀] [Algebra.IsAlgebraic k K]
    (hC : AlgebraicCurve.ConstantsAreBase k F₀)
    (hgen : Algebra.adjoin F₀ (Set.range (algebraMap K F)) = ⊤) :
    ∃ φ : F →ₐ[K] F, ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k) := by sorry
