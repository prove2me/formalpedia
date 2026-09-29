-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
-- name    : AlgebraicCurve.Place.exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/c3816fd4-691f-50a0-ac99-8e99e4bdbb85
-- title:
--   Local subring of a function field is dominated by a place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $x \in F$ be such that $F$ is finite-dimensional over the intermediate field $K(x) =$ `IntermediateField.adjoin K {x}`. Let $D$ be a subring of $F$ which is a local ring, assume that $\operatorname{algebraMap} K F (a) \in D$ for every $a \in K$, and assume that $D$ contains an element $d$ with $d \neq 0$ and $d$ not a unit of $D$. The conclusion asserts the existence of a place $Q$ of $F$ over $K$ in the sense of the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), that is, a valuation subring $\mathcal{O}_Q = Q.\text{toValuationSubring}$ of $F$ which contains the image of every element of $K$, is not the whole of $F$, and whose underlying ring is a principal ideal ring, such that: first, every $d \in F$ lying in $D$ lies in $\mathcal{O}_Q$; and second, for every $d \in D$, the image of $d$ in $F$ lies in the non-units of $\mathcal{O}_Q$ (equivalently, in the maximal ideal of $\mathcal{O}_Q$) if and only if $d$ is not a unit of $D$. Thus $Q$ dominates $D$: $D \subseteq \mathcal{O}_Q$ and $D \cap \mathfrak{m}_Q = \mathfrak{m}_D$.
--
--   This is Chevalley's extension theorem in the setting of a one-variable function field: a local subring of $F$ containing the constants and having a non-zero non-unit is dominated by a place of $F/K$. It is used to produce the place at which an integral model of a modular curve is read at a good point, and is cited by the results on two-chart integral models and on the existence of readings at good points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Subring F) [IsLocalRing D] (hK : ∀ a : K, algebraMap K F a ∈ D)
    (hD : ∃ d : D, d ≠ 0 ∧ ¬ IsUnit d) :
    ∃ Q : AlgebraicCurve.Place K F, (∀ d : F, d ∈ D → d ∈ Q.toValuationSubring) ∧
      ∀ d : D, ((d : F) ∈ Q.toValuationSubring.nonunits ↔ ¬ IsUnit d) := by sorry
