-- Prove2me | Theorems.Thm_AddMonoidAlgebra_finite_setOf_withConv_algHom_pow_eq_one
-- name    : AddMonoidAlgebra.finite_setOf_withConv_algHom_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/26cc2cd1-4a21-5ad1-8116-e7eae4d996d0
-- title:
--   Finiteness of n-torsion characters of κ[ℤ^t]
-- statement:
--   Let $\kappa$ be a commutative ring which is an integral domain, let $t, n$ be natural numbers and assume $n > 0$. Consider the $\kappa$-algebra homomorphisms from the group algebra $\mathrm{AddMonoidAlgebra}\ \kappa\ (\mathrm{Fin}\ t \to \mathbb{Z})$, i.e. $\kappa[\mathbb{Z}^t]$, to $\kappa$, equipped through the type synonym `WithConv` with the monoid structure given by convolution: the product of $\chi$ and $\chi'$ is the composite of the comultiplication of the group bialgebra with $\chi \otimes \chi'$ followed by multiplication on $\kappa$, and the unit is the counit. The assertion is that the set of those $\chi$ in this convolution monoid satisfying $\chi^n = 1$ is a finite subset. Concretely, the characters of the split torus of rank $t$ over $\kappa$ whose $n$-th convolution power is the counit form a finite set; no bound on the cardinality is asserted, and no hypothesis on roots of unity in $\kappa$ is imposed.
--
--   This is the finiteness of the $n$-torsion in the group of $\kappa$-points of the split torus $\mathbb{G}_m^t$ over an integral domain, in the bialgebra formulation: points are characters $\kappa[\mathbb{Z}^t] \to \kappa$ under convolution. It is used in the verification that the fibres of multiplication by $n$ on certain group schemes attached to Deligne–Rapoport models of modular curves are quasi-finite, in [`ModularCurve.DRModelPackageLevel.locallyQuasiFinite_fibre_schemeNsmul_of_not_isUnit`](thm.html#ModularCurve.DRModelPackageLevel.locallyQuasiFinite_fibre_schemeNsmul_of_not_isUnit) and [`ModularCurve.XHDRModelAtP.locallyQuasiFinite_fibre_schemeNsmul_of_not_isUnit`](thm.html#ModularCurve.XHDRModelAtP.locallyQuasiFinite_fibre_schemeNsmul_of_not_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidAlgebra_finite_setOf_withConv_algHom_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem AddMonoidAlgebra.finite_setOf_withConv_algHom_pow_eq_one
    (κ : Type u) [CommRing κ] [IsDomain κ] (t n : ℕ) (hn : 0 < n) :
    {χ : WithConv (AddMonoidAlgebra κ (Fin t → ℤ) →ₐ[κ] κ) | χ ^ n = 1}.Finite := by sorry
