-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap
-- name    : AlgebraicCurve.Place.exists_toValuationSubring_eq_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/30a3796c-a370-52ad-a290-6d595cf72e66
-- title:
--   Restriction of a place along an integral extension
-- statement:
--   Let $K$, $F$, $F'$ be fields, with $F$ and $F'$ equipped with $K$-algebra structures, $F'$ with an $F$-algebra structure, the three forming a scalar tower $K \subseteq F \subseteq F'$, and with $F'$ integral over $F$. Here a `Place K F` is a valuation subring $\mathcal O \subseteq F$ such that the image of $K$ under $\operatorname{algebraMap} K F$ is contained in $\mathcal O$, such that $\mathcal O \neq F$, and such that $\mathcal O$ is a principal ideal ring; likewise for `Place K F'`. The assertion is that for every place $w$ of $F'$ over $K$ there exists a place $v$ of $F$ over $K$ whose valuation subring is the preimage of the valuation subring of $w$ under $\operatorname{algebraMap} F F'$, that is, $\mathcal O_v = \mathcal O_w \cap F$. Thus the intersection of $\mathcal O_w$ with $F$ again contains $K$, is a proper valuation subring of $F$, and is a principal ideal ring. The statement is purely existential: no restriction operation is named, and uniqueness of $v$ (automatic, since a place is determined by its valuation subring) is not part of the conclusion.
--
--   This is the restriction $w \mapsto w|_F$ of places along an algebraic extension of fields over a common base field, in the form needed to compare places of a function field with those of a subfield. It is used in the treatment of the modular function field, for the description of the $j$-coordinate via [`ModularCurve.jCoordinate_spec_modularFunctionFieldBar`](thm.html#ModularCurve.jCoordinate_spec_modularFunctionFieldBar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F') : ∃ v : Place K F, v.toValuationSubring = w.toValuationSubring.comap (algebraMap F F') := by sorry
