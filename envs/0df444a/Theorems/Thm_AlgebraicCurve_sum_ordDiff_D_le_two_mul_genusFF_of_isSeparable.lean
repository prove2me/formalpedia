-- Prove2me | Theorems.Thm_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable
-- name    : AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/5d02ada5-b26c-53f6-be3d-8cb835c86687
-- title:
--   Hurwitz genus inequality for F/k(x) in differential form
-- statement:
--   Let $k$ be an algebraically closed field, $F$ a field with a $k$-algebra structure, and $x \in F$ transcendental over $k$; assume $F$ is finite-dimensional over the intermediate field $k(x) =$ `IntermediateField.adjoin k {x}` and separable over it. Places of $F/k$ are the valuation subrings of $F$ containing $k$, distinct from $F$ itself and principal ideal rings; for such a place $P$, $\operatorname{ord}_P$ is the associated normalised additive valuation (minus the logarithm of the adic valuation attached to $P$), and $\operatorname{ordDiff}_P(\omega)$ is $\operatorname{ord}_P$ of the coefficient $g \in F$ for which $\omega = g \cdot D\,t$, where $t$ is a chosen element of $F$ with $\operatorname{ord}_P t = 1$ and $D$ is the universal derivation into $\Omega_{F/k}$. Let $T$ be a finite set of places at which $x$ is regular, i.e. $\operatorname{ord}_P x \ge 0$ for all $P \in T$, and $T_\infty$ a finite set of places at which $x$ has a pole, i.e. $\operatorname{ord}_P x < 0$ for all $P \in T_\infty$. Then $$\sum_{P \in T} \operatorname{ordDiff}_P(D x) + \sum_{P \in T_\infty} (-\operatorname{ord}_P x - 1) \le 2\,g - 2 + 2\,[F : k(x)],$$ where $g = \dim_k H^1(0)$ is `genusFF k F`. No disjointness of $T$ and $T_\infty$, and no exhaustiveness, is required.
--
--   This is the Riemann–Hurwitz genus formula for the separable extension $F/k(x)$, in the one-sided form of an inequality obtained by summing local contributions of the canonical divisor class of $dx$ over arbitrary finite sets of regular points and poles of $x$ and discarding the remaining nonnegative different exponents; as such it is valid in arbitrary characteristic, including wild ramification. It underlies the genus estimates for the function fields of modular curves used in the comparison of the genera of coverings, and is cited by [`AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable`](thm.html#AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable) and by the genus comparison [`ModularCurve.genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd`](thm.html#ModularCurve.genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T : Finset (Place k F)) (hT : ∀ P ∈ T, 0 ≤ P.ord x)
    (Tinf : Finset (Place k F)) (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, P.ordDiff (KaehlerDifferential.D k F x) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by sorry
