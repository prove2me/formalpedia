-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_taylorRem_mem_toValuationSubring
-- name    : AlgebraicCurve.Place.taylorRem_mem_toValuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/7294b11b-9f14-561b-854a-4896003534a6
-- title:
--   Taylor remainders along a uniformiser stay in the valuation ring
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project, that is, a valuation subring $\mathcal{O}_v \subseteq F$ containing the image of $K$ under the structure map, different from all of $F$, and whose underlying ring is a principal ideal ring. Assume $v$ is rational, meaning that the composite map from $K$ to the residue field $\mathcal{O}_v/\mathfrak{m}_v$ is surjective. Let $t \in F$ satisfy $\operatorname{ord}_v t = 1$, where $\operatorname{ord}_v$ is minus the logarithm of the associated adic valuation, so $t$ is a uniformiser at $v$. Let $f \in \mathcal{O}_v$ and let $r$ be a natural number. Then the $r$-th Taylor remainder $\rho_r = \mathrm{taylorRem}\ v\ t\ f\ r$ again lies in $\mathcal{O}_v$, where the remainders are defined recursively by $\rho_0 = f$ and $\rho_{r+1} = (\rho_r - \iota(\mathrm{evalAt}_v\,\rho_r))\,t^{-1}$, with $\iota \colon K \to F$ the structure map and $\mathrm{evalAt}_v$ the $K$-valued evaluation at $v$ (the inverse image in $K$ of the residue class of an element of $\mathcal{O}_v$, and $0$ on elements outside $\mathcal{O}_v$).
--
--   This is the basic regularity statement underlying Taylor expansion of a function regular at a rational place along a uniformiser: it guarantees that each Taylor coefficient $a_r = \mathrm{evalAt}_v \rho_r$ is a genuine value rather than the default value assigned outside the valuation ring. It is used in establishing additivity, multiplicativity and $K$-linearity of the Taylor coefficients, via [`AlgebraicCurve.Place.taylorCoeff_add`](thm.html#AlgebraicCurve.Place.taylorCoeff_add), [`AlgebraicCurve.Place.taylorCoeff_mul`](thm.html#AlgebraicCurve.Place.taylorCoeff_mul) and [`AlgebraicCurve.Place.taylorCoeff_smul`](thm.html#AlgebraicCurve.Place.taylorCoeff_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_taylorRem_mem_toValuationSubring.lean

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.taylorRem_mem_toValuationSubring
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (r : ℕ) :
    taylorRem v t f r ∈ v.toValuationSubring := by sorry
