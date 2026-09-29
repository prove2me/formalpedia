-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_sub_algebraMap_mem_maximalIdeal
-- name    : AlgebraicCurve.Place.exists_sub_algebraMap_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/300032aa-ff0b-5e54-9ae6-edb69a5d935d
-- title:
--   Degree-one places: integers are constants modulo 𝔪
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $u$ be a place of $F$ over $K$ in the sense of the project: a valuation subring $u.\mathtt{toValuationSubring}$ of $F$ which contains the image of $K$ under the structure map, which is not all of $F$, and whose ideals are all principal. Assume that the degree of $u$, defined as the $K$-module rank $\mathrm{finrank}_K$ of the residue field $\mathrm{IsLocalRing.ResidueField}$ of $u.\mathtt{toValuationSubring}$, equals $1$. Then for every element $b$ of the valuation ring $u.\mathtt{toValuationSubring}$ there exists a scalar $c \in K$ such that $b - \mathrm{algebraMap}_K(c)$ lies in the maximal ideal of the local ring $u.\mathtt{toValuationSubring}$; here $\mathrm{algebraMap}_K(c)$ denotes the image of $c$ in the valuation ring under the induced $K$-algebra structure. In other words, at a place of degree one the composite $K \to u.\mathtt{toValuationSubring} \to$ residue field is surjective on the level of elements: every integer at $u$ is congruent modulo the maximal ideal to a constant.
--
--   This is the elementary form of the statement that the residue field at a degree-one (rational) place is the constant field $K$, so that reduction at such a place takes values in $K$. It is used in the project wherever a rational place is used to evaluate functions, for instance in the constant-reduction and Riemann–Roch estimates that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_sub_algebraMap_mem_maximalIdeal.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.exists_sub_algebraMap_mem_maximalIdeal {K F : Type*} [Field K] [Field F]
    [Algebra K F] (u : AlgebraicCurve.Place K F) (hdeg : u.deg = 1) (b : u.toValuationSubring) :
    ∃ c : K, b - algebraMap K u.toValuationSubring c
      ∈ IsLocalRing.maximalIdeal u.toValuationSubring := by sorry
