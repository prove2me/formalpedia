-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_bijective_appTop_toBase
-- name    : AlgebraicCurve.SemistableModel.bijective_appTop_toBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/ef21aaab-1ede-5977-ba24-d4c2838a95ae
-- title:
--   Global sections of a semistable model are A
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$. Fix index types $\iota_V, \iota_E$, fields $\bar F_i$ ($i \in \iota_V$) over the residue field of $A$, component charts $C_i \in$ `ComponentChart A F (Fbar i)`, annuli $\mathrm{An}_e \in$ `Annulus A F` ($e \in \iota_E$), maps $\mathrm{src}, \mathrm{tgt} : \iota_E \to \iota_V$ and places $x_s(e)$, $x_t(e)$ of $\bar F_{\mathrm{src}(e)}$, resp. $\bar F_{\mathrm{tgt}(e)}$, over the residue field of $A$, and let $M$ be a semistable model for these data in the sense of the structure `SemistableModel`: an integral scheme $X$ with a proper, flat morphism `M.toBase` $: X \to \operatorname{Spec} A$ locally of finite presentation, an isomorphism `M.ffEquiv` of $F$ with the function field of $X$ carrying $A \subseteq L$ to the sections pulled back from the base, points of $X$ attached to the places of $F/L$ (with prescribed local rings inside $F$, lying over the generic point of $\operatorname{Spec} A$), to the chart generic points, to the non-nodal places of the $\bar F_i$ and to the annuli, classifying all points of $X$ bijectively, together with the remaining incidence and specialisation conditions. Assume moreover `IsCurveOver L F`: every nonzero $f \in F$ has a divisor, supported on the places of $F/L$, recording $\mathrm{ord}_v(f)$ at every place and of degree $0$; every place of $F/L$ has residue field finite over $L$; and $\Omega_{F/L}$ is free of rank one over $F$. Assume also that $F$ is essentially of finite type over $L$. Then the ring homomorphism on global sections induced by `M.toBase`, from $\Gamma(\operatorname{Spec} A, \mathcal O)$ to $\Gamma(X, \mathcal O_X)$, is bijective.
--
--   This is the statement that a semistable model $X \to \operatorname{Spec} A$ of a one-variable function field over an algebraically closed field has no global functions beyond the constants of the base, $\Gamma(X, \mathcal O_X) = A$. It is used in the transfer of Picard-group data along a semistable model over a (possibly non-noetherian) valuation ring to a finite level, by the two results producing Kummer Cartier data at finite level from Cartier data on such a model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_bijective_appTop_toBase.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.bijective_appTop_toBase
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt) [IsCurveOver L F] [Algebra.EssFiniteType L F] :
    Function.Bijective M.toBase.appTop := by sorry
