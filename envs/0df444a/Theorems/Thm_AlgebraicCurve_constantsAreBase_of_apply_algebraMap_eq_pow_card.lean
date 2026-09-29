-- Prove2me | Theorems.Thm_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card
-- name    : AlgebraicCurve.constantsAreBase_of_apply_algebraMap_eq_pow_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/9ce50c12-7ccd-5018-9425-9a250c15862a
-- title:
--   Full constant field from a relative q-Frobenius
-- statement:
--   Let $k$ be a finite field, $K$ an algebraically closed field, and $F_0$, $F$ fields, equipped with algebra structures $k \to F_0$, $F_0 \to F$ and $K \to F$ (no compatibility between these is assumed). Suppose $F$ is a curve over $K$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ admits a divisor $D$ on the places of $F/K$ (valuation subrings of $F$ containing the image of $K$, proper and with principal maximal ideal) with $D(v) = v.\mathrm{ord}(f)$ for all $v$ and $\deg D = 0$; every place of $F/K$ has residue field finite-dimensional over $K$; and $\Omega_{F/K}$ is free of rank $1$ over $F$. Assume further that $F_0$ is generated over $k$, as a field, by a finite subset; that the image of $F_0$ in $F$ generates $F$ over $K$ as a field; and that there is a $K$-algebra endomorphism $\varphi$ of $F$ with $\varphi(x) = x^{q}$ for every $x$ in the image of $F_0$, where $q = \#k$. Then [`AlgebraicCurve.ConstantsAreBase k F₀`](def/AlgebraicCurve_AdelicIndex.html#L45) holds: the Riemann–Roch space $L(0)$ of the zero divisor of $F_0/k$ coincides with the image of $k$ in $F_0$ under $k \to F_0$.
--
--   This is the statement that $k$ is the full constant field of the function field $F_0$, in the situation where $F_0$ is presented together with a base change $F$ to an algebraically closed field carrying a relative $q$-Frobenius; in that situation the condition is automatic rather than an extra hypothesis. It is invoked by the counting statements for divisor class groups of curves over finite fields, such as the Abel–Jacobi and fixed-point counting results for $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.constantsAreBase_of_apply_algebraMap_eq_pow_card
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    AlgebraicCurve.ConstantsAreBase k F₀ := by sorry
