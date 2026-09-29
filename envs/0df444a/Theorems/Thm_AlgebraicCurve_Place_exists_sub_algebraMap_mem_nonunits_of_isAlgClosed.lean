-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed
-- name    : AlgebraicCurve.Place.exists_sub_algebraMap_mem_nonunits_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/40bc99a1-3ae3-5727-bc86-970e38ced2e5
-- title:
--   Rationality of places with finite residue over an algebraically closed field
-- statement:
--   Let $\kappa'$ be an algebraically closed field and $F'$ a field equipped with a $\kappa'$-algebra structure, and let $P'$ be a place of $F'$ over $\kappa'$ in the sense of the project's structure `Place`: a valuation subring $\mathcal{O}_{P'} =$ `P'.toValuationSubring` of $F'$ which contains the image of $\kappa'$ under the structure map, is not all of $F'$, and is a principal ideal ring. Assume moreover that $P'$ has finite residue, i.e. the residue field $\mathcal{O}_{P'}/\mathfrak{m}_{P'}$ of the local ring $\mathcal{O}_{P'}$ is finite-dimensional as a $\kappa'$-module. Then for every $x \in F'$ lying in $\mathcal{O}_{P'}$ there exists a constant $c \in \kappa'$ such that $x - \mathrm{algebraMap}_{\kappa' \to F'}(c)$ lies in `P'.toValuationSubring.nonunits`, the set of elements of $F'$ whose image in $\mathcal{O}_{P'}$ is a non-unit; equivalently, $x - c$ belongs to the maximal ideal $\mathfrak{m}_{P'}$. Thus every element of the valuation ring is congruent to a constant modulo the maximal ideal, so that $P'$ is a rational (degree-one) place.
--
--   This is the classical statement that a place of a function field over an algebraically closed constant field, with residue field finite over that constant field, is rational: the residue field is then equal to $\kappa'$. It is used in the comparison of algebra homomorphisms through restriction along places in characteristic zero, and in the analysis of inertia at points of the integral model of $X_0(p)$-type modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped Pointwise

theorem AlgebraicCurve.Place.exists_sub_algebraMap_mem_nonunits_of_isAlgClosed
    {κ' : Type*} [Field κ'] [IsAlgClosed κ'] {F' : Type*} [Field F'] [Algebra κ' F']
    (P' : Place κ' F') [P'.FiniteResidue]
    (x : F') (hx : x ∈ P'.toValuationSubring) :
    ∃ c : κ', x - algebraMap κ' F' c ∈ P'.toValuationSubring.nonunits := by sorry
