-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic
-- name    : AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/8330e00a-fde6-5258-962b-05322f5a83d1
-- title:
--   Prime-to-p torsion of Pic⁰ over 𝔽̄_q
-- statement:
--   Let $k$ be a finite field, $K$ an algebraically closed field, and $F_0$, $F$ fields with $F_0$ a $k$-algebra, $F$ a $K$-algebra and also an $F_0$-algebra, such that $F_0$ is a curve over $k$ and $F$ is a curve over $K$ in the project's sense: every nonzero function has a divisor recording its orders at all places, that divisor having degree zero; every place has residue field finite-dimensional over the base field; and the module of Kähler differentials is free of rank one over the function field. Assume: $F_0$ is generated as a field over $k$ by a finite subset; the subfield of $F$ generated over $K$ by the image of $F_0$ is all of $F$; every $a \in K$ satisfies $a^{q^n} = a$ for some $n > 0$, where $q = \#k$; there is a $K$-algebra endomorphism $\varphi$ of $F$ whose restriction to the image of $F_0$ is the $q$-th power map, i.e. $\varphi(x) = x^{q}$ for $x$ in the image of $F_0$; and $\ell$ is a prime whose image in $K$ is nonzero. Then, writing $g$ for the genus $\dim_K H^1(0)$ of $F/K$ and $\mathrm{Pic}^0(F/K)$ for the quotient of the group of degree-zero divisors on the places of $F/K$ by the subgroup of principal divisors, for every $n$ the subgroup of elements killed by $\ell^n$ has exactly $\ell^{2gn}$ elements (in particular it is finite, as the asserted cardinality is nonzero).
--
--   This is the classical determination of the prime-to-$p$ torsion of the Jacobian of a curve over the algebraic closure of a finite field, $\#J[\ell^n] = \ell^{2gn}$, in the divisor-class-group formulation and under the hypothesis that the curve is obtained by constant field extension from a curve over $k$, witnessed by a relative $q$-Frobenius endomorphism $\varphi$. It feeds the version [`AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius`](thm.html#AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius) and the count of $\ell$-torsion [`AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_two_mul_genusFF_of_forall_pow_eq_self`](thm.html#AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_two_mul_genusFF_of_forall_pow_eq_self), which supply the $2g$-dimensionality of Tate modules used later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card k ^ n = a)
    (φ : F →ₐ[K] F)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    AlgebraicCurve.AbelJacobiCard K F ℓ (AlgebraicCurve.genusFF K F) := by sorry
