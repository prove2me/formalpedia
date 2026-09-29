-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_valuation_evalAt_param_sub_algebraMap
-- name    : AlgebraicCurve.Annulus.valuation_evalAt_param_sub_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/145c44b2-fa1b-5bfb-85e8-f40aeacca4e8
-- title:
--   Valuation of a translate of the annulus parameter at a place
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field equipped with an $L$-algebra structure. Let $An$ be an annulus for $A$ in $F$, so in particular $An$ carries a set $An.dom$ of places of $F$ over $L$ (valuation subrings of $F$ containing $\mathrm{image}(L)$, proper, with principal ideals) and a parameter $An.param \in F$ whose value at each place of $An.dom$ lies in the maximal ideal of $A$ and is non-zero. Let $P$ be a place of $F$ over $L$ lying in $An.dom$, write $z(P) := P.evalAt\,An.param \in L$ for the value of the parameter at $P$ (the element of $L$ representing the residue class of $An.param$ in the residue field of $P$), and let $a \in L$. Then, denoting by $v$ the valuation attached to $A$: first, if $v(z(P)) \ne v(a)$ then $v\bigl(P.evalAt(An.param - a)\bigr) = \max\bigl(v(z(P)), v(a)\bigr)$; second, if $v(z(P)) = v(a)$ then $v\bigl(P.evalAt(An.param - a)\bigr) \le v(a)$, and moreover, if $a \ne 0$ and $a^{-1} z(P)$ lies in $A$, then equality $v\bigl(P.evalAt(An.param - a)\bigr) = v(a)$ holds if and only if the residue of $a^{-1} z(P)$ in the residue field of $A$ is different from $1$. Here $a$ is viewed in $F$ through the structure map, and $P.evalAt$ of an element outside the valuation subring of $P$ is $0$ by convention.
--
--   This is the pointwise profile, at a single place of an annulus, of the translate $An.param - a$ of the parameter: the ultrametric inequality for $A$ together with the description of the boundary case, equality failing exactly when $z(P)/a$ reduces to $1$. It is used in the study of which functions become units or have prescribed valuation on sub-annuli, being cited by [`AlgebraicCurve.Annulus.exists_valuationSubring_mem_iff_of_valuation_lt`](thm.html#AlgebraicCurve.Annulus.exists_valuationSubring_mem_iff_of_valuation_lt), [`AlgebraicCurve.Annulus.mapDomain_and_slope_of_valuation_lt_of_exists_lt`](thm.html#AlgebraicCurve.Annulus.mapDomain_and_slope_of_valuation_lt_of_exists_lt) and [`AlgebraicCurve.Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt`](thm.html#AlgebraicCurve.Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_valuation_evalAt_param_sub_algebraMap.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.Annulus.valuation_evalAt_param_sub_algebraMap
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F) (P : Place L F) (hP : P ∈ An.dom) (a : L) :
    (A.valuation (P.evalAt An.param) ≠ A.valuation a →
        A.valuation (P.evalAt (An.param - algebraMap L F a)) =
          max (A.valuation (P.evalAt An.param)) (A.valuation a)) ∧
      (A.valuation (P.evalAt An.param) = A.valuation a →
        A.valuation (P.evalAt (An.param - algebraMap L F a)) ≤ A.valuation a ∧
          (a ≠ 0 → ∀ h : a⁻¹ * P.evalAt An.param ∈ A,
            (A.valuation (P.evalAt (An.param - algebraMap L F a)) = A.valuation a ↔
              IsLocalRing.residue A ⟨a⁻¹ * P.evalAt An.param, h⟩ ≠ 1))) := by sorry
