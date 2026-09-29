-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring
-- name    : AlgebraicCurve.Place.exists_comap_eq_toValuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/f0a94d62-2b84-5ebf-8d4e-17901b985295
-- title:
--   Places extend along finite separable extensions
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ both $K$-algebras, $F'$ an $F$-algebra, the three structures compatible ($K \to F \to F'$ a scalar tower), $F'/F$ finite-dimensional and separable. Here a place of a field extension $E/K$ is a valuation subring $\mathcal{O} \subseteq E$ such that the image of $K$ in $E$ is contained in $\mathcal{O}$, such that $\mathcal{O} \neq E$, and such that $\mathcal{O}$ is a principal ideal ring; the data `toValuationSubring` records the valuation subring itself. The assertion is that for every place $v$ of $F/K$ there exists a place $w$ of $F'/K$ whose valuation subring pulls back to that of $v$ along the structure map $F \to F'$: the preimage (`comap`) of $w$'s valuation subring under $\mathrm{algebraMap}\, F\, F'$ equals $v$'s valuation subring. Equivalently, the restriction map from places of $F'/K$ to places of $F/K$ is surjective; no claim is made here about the number of such $w$, nor about ramification indices or residue degrees.
--
--   This is the existence half of the classical extension theorem for places of function fields: every place of $F/K$ lies below at least one place of a finite separable extension $F'$. It is used in the project's treatment of places, orders and divisors, for instance in deducing the existence of a place with negative order at a transcendental element, in the multiplicativity of order along an extension, and in the criterion for an element with everywhere non-negative order to lie in the constant field over an algebraically closed base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_comap_eq_toValuationSubring {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) : ∃ w : Place K F', w.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring := by sorry
