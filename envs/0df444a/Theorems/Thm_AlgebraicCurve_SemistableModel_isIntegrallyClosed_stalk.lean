-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_isIntegrallyClosed_stalk
-- name    : AlgebraicCurve.SemistableModel.isIntegrallyClosed_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/b33c3ca7-d89c-5ee0-8276-1b60bfd40de9
-- title:
--   Stalks of a semistable model are integrally closed
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$. Let $\iota_V$, $\iota_E$ be index types, let $(\bar F_i)_{i \in \iota_V}$ be fields each equipped with an algebra structure over the residue field of $A$, let $C_i$ be a `ComponentChart` for $A$, $F$, $\bar F_i$ (a valuation subring of $F$ whose intersection with $L$ is $A$, together with a surjective residue map onto $\bar F_i$ with kernel the maximal ideal, a set of places of $F/L$ in its domain, a finite set of nodal places of $\bar F_i$, and a place map compatible with evaluation and with orders of functions), let $An_e$ be annuli for $A$, $F$ (a set of rational places of $F/L$, a parameter, a modulus in the maximal ideal of $A$, with the stated bijective parametrisation of the places of the annulus by their evaluations, order-one behaviour of the parameter, and the unit principle), let $\mathrm{src}, \mathrm{tgt} : \iota_E \to \iota_V$, and let $x_s(e)$, $x_t(e)$ be places of $\bar F_{\mathrm{src}(e)}$, $\bar F_{\mathrm{tgt}(e)}$ over the residue field of $A$. Let $M$ be a `SemistableModel` for these data: in particular an integral scheme $X = M.X$ with a proper, flat, locally of finite presentation morphism to $\operatorname{Spec} A$, an isomorphism of $F$ with the function field of $X$ compatible with $A$, and the dictionary assigning points of $X$ to places, components, smooth special points and nodes, bijectively, with their local rings identified inside $F$. Then for every point $x$ of $X$ the stalk $\mathcal{O}_{X,x}$ is integrally closed in its field of fractions.
--
--   This is the normality of a semistable model: all local rings of the underlying scheme are integrally closed domains. It supplies the normal-stalk hypothesis in the finite-descent construction for semistable models, [`AlgebraicCurve.SemistableModel.Descent.exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter`](thm.html#AlgebraicCurve.SemistableModel.Descent.exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_isIntegrallyClosed_stalk.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.isIntegrallyClosed_stalk
    {L : Type u} [Field L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt) (x : M.X) :
    IsIntegrallyClosed (M.X.presheaf.stalk x) := by sorry
