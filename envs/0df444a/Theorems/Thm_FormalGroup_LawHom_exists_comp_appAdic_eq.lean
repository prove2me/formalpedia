-- Prove2me | Theorems.Thm_FormalGroup_LawHom_exists_comp_appAdic_eq
-- name    : FormalGroup.LawHom.exists_comp_appAdic_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/e39a05ec-6f8c-50b1-81d5-e984da564867
-- title:
--   Adic evaluation of a composite formal group law homomorphism
-- statement:
--   Let $R$ be a commutative ring (in universe $u$) and let $F$, $G$, $H$ be formal group laws over $R$. Let $\varphi$ be a homomorphism from $F$ to $G$ and $\chi$ a homomorphism from $G$ to $H$, where a homomorphism in this sense consists of a one-variable power series over $R$ with vanishing constant coefficient that satisfies the compatibility $\varphi(F(X_0,X_1)) = G(\varphi(X_0),\varphi(X_1))$, expressed as the equality of the substitution of `F.toPowerSeries` into the series with the substitution of the pair of series $\varphi(X_0), \varphi(X_1)$ into `G.toPowerSeries`. The assertion is that there exists a homomorphism $\omega$ from $F$ to $H$ with two properties: first, its underlying power series is the substitution of $\varphi$'s series into $\chi$'s series, i.e. $\omega(X) = \chi(\varphi(X))$; second, for every commutative $R$-algebra $A$ in universe $u$, every ideal $I \subseteq A$ such that $A$ is $I$-adically complete, and every $a \in I$, the $I$-adic evaluation satisfies $\omega.\mathrm{appAdic}\,I\,a = \chi.\mathrm{appAdic}\,I\,(\varphi.\mathrm{appAdic}\,I\,a)$, where `appAdic` denotes evaluation of the series at the point, taken with respect to the $I$-adic topology on $A$.
--
--   This records that composition of formal group law homomorphisms, defined on the level of power series by substitution, is computed pointwise on adically complete algebras: the induced maps on $I$-adic points compose. It is used in the comparisons of level structures and of Drinfeld bases on the formal groups attached to the relevant moduli packages, for instance by [`FormalGroup.LawHom.appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X`](thm.html#FormalGroup.LawHom.appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X) and by the existence statements for raw law isomorphisms with prescribed adic behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_LawHom_exists_comp_appAdic_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

theorem FormalGroup.LawHom.exists_comp_appAdic_eq
    {R : Type u} [CommRing R] {F G H : FormalGroup R} (φ : FormalGroup.LawHom F G) (χ : FormalGroup.LawHom G H) :
    ∃ ω : FormalGroup.LawHom F H,
      ω.series = PowerSeries.subst φ.series χ.series ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A) [IsAdicComplete I A] (a : A), a ∈ I →
        ω.appAdic I a = χ.appAdic I (φ.appAdic I a) := by sorry
