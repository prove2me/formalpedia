-- Prove2me | Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
-- name    : AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/af369c52-de99-50f1-8746-68c304bb1774
-- title:
--   Fixed places of iterated Frobenius count places of F₀
-- statement:
--   Let $k$ be a finite field, $K$ an algebraically closed field, and $F_0$, $F$ fields with $k$-algebra, $K$-algebra and $F_0$-algebra structures on $F_0$, $F$ and $F$ respectively. Assume $F_0$ is a curve over $k$ and $F$ is a curve over $K$ in the project's sense: principal divisors exist (every nonzero function is the divisor of some degree-zero divisor giving its order at each place), every place has residue field finite over the base field, and the module of Kähler differentials is free of rank one over the function field. Here a place of $F/K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring; its degree is the $K$-dimension of its residue field. Assume further that $F_0$ is generated over $k$ by a finite subset (`hfg`), that adjoining the image of $F_0$ to $K$ inside $F$ gives all of $F$ (`hgen`), and let $\varphi : F \to F$ be a $K$-algebra endomorphism whose underlying ring homomorphism is integral (every element of $F$ is integral over the image) and which satisfies $\varphi(x) = x^{\#k}$ for all $x$ in the image of $F_0$ (`hφ`). Write $\mathrm{Fr}$ for the map `Place.restrictAlong φ hφi` on places of $F/K$, sending $w$ to the place whose valuation subring is the preimage $\varphi^{-1}(\mathcal{O}_w)$. Then for every $r > 0$ the set of fixed points of the $r$-th iterate of $\mathrm{Fr}$ is finite and its cardinality equals $\sum_{d \mid r} d \cdot \#\{v \text{ a place of } F_0/k : \deg v = d\}$.
--
--   This is the dictionary between the geometric and arithmetic point counts for a curve over a finite field: the places of the constant-field extension $F = K \cdot F_0$ fixed by the $r$-th power of the relative Frobenius are precisely those lying over a place of $F_0$ whose degree divides $r$, with exactly $d$ of them above a place of degree $d$. It feeds the computation of the order of $\mathrm{Pic}^0$ and of the value of the zeta function used in the counting results that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (r : ℕ) (hr : 0 < r) :
    (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[r]).Finite ∧
      Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[r]) =
        ∑ d ∈ Nat.divisors r, d * Nat.card {v : AlgebraicCurve.Place k F₀ | v.deg = d} := by sorry
