-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq
-- name    : AlgebraicCurve.Place.exists_restrict_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/f6b444ba-53d9-5bdc-92a4-aac9a9e883e6
-- title:
--   Every place extends to a finite separable extension
-- statement:
--   Let $K$, $F'$ and $M$ be fields with $K$-algebra structures on $F'$ and $M$ and an $F'$-algebra structure on $M$ forming a scalar tower over $K$, and assume $M$ is finite-dimensional and separable over $F'$. A place of a field $F$ over $K$, in the sense used here, is a valuation subring $\mathcal{O}$ of $F$ which contains $\operatorname{im}(K \to F)$, is not all of $F$, and is a principal ideal ring; its restriction along $F' \to M$ is the place of $F'$ whose valuation subring is the preimage of $\mathcal{O}$ under $\operatorname{algebraMap} F' M$ (the three defining conditions being inherited). The assertion is: for every place $w$ of $F'$ over $K$ there exists a place $W$ of $M$ over $K$ whose restriction to $F'$ equals $w$, i.e. the restriction map on places along a finite separable extension is surjective.
--
--   This is the finite separable case of Chevalley's extension theorem for places, equivalently surjectivity of the restriction map $\operatorname{Place}(M/K) \to \operatorname{Place}(F'/K)$. It is used throughout the curve-theoretic part of the development, for instance in the injectivity arguments for the divisorial Weil pairing and in the extension of places along subfields of finite degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_restrict_eq.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Mathlib.FieldTheory.Separable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_restrict_eq {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [Algebra.IsSeparable F' M] (w : Place K F') :
    ∃ W : Place K M, W.restrict F' = w := by sorry
