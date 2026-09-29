-- Prove2me | Theorems.Thm_FormalGroup_LawHom_exists_comp_series_eq_subst
-- name    : FormalGroup.LawHom.exists_comp_series_eq_subst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/b9b35e6f-6d67-5aaf-95d7-b6090b13d531
-- title:
--   Composition of formal group law homomorphisms
-- statement:
--   Let $R$ be a commutative ring and let $F$, $G$, $H$ be one-dimensional formal group laws over $R$, each given by a two-variable power series `toPowerSeries` with vanishing constant coefficient. Let $\theta$ be a homomorphism from $F$ to $G$ and $\eta$ a homomorphism from $G$ to $H$ in the sense of the project structure `LawHom`: thus $\theta$ consists of a one-variable power series $\theta.\mathrm{series} \in R[[X]]$ with $\theta.\mathrm{series}(0)=0$ satisfying the identity $\theta.\mathrm{series}\bigl(F(X_0,X_1)\bigr) = G\bigl(\theta.\mathrm{series}(X_0),\,\theta.\mathrm{series}(X_1)\bigr)$ in $R[[X_0,X_1]]$, where substituting $X_i$ into a series is the operation `LawHom.substX`, and similarly for $\eta$ with $F$, $G$ replaced by $G$, $H$. The assertion is that there exists a homomorphism $\kappa$ from $F$ to $H$ — that is, a series with zero constant coefficient satisfying the corresponding identity for $F$ and $H$ — whose underlying series is the substitution $\eta.\mathrm{series}(\theta.\mathrm{series}(X))$, and whose coefficient of $X$ equals the product of the coefficients of $X$ in $\eta.\mathrm{series}$ and in $\theta.\mathrm{series}$. The statement is an existence statement rather than the construction of a composition operation on `LawHom`.
--
--   This is the standard fact that homomorphisms of one-dimensional formal group laws compose by substitution of power series, and that the induced map on tangent spaces (the linear coefficient) is multiplicative. It is used throughout the project's formal-group material, for instance in [`FormalGroup.LawHom.exists_comp_appAdic_eq`](thm.html#FormalGroup.LawHom.exists_comp_appAdic_eq) and in the rigidity and Hasse-invariant arguments for Drinfeld-type bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_LawHom_exists_comp_series_eq_subst.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.LawHom.exists_comp_series_eq_subst
    {R : Type u} [CommRing R] {F G H : FormalGroup R}
    (θ : FormalGroup.LawHom F G) (η : FormalGroup.LawHom G H) :
    ∃ κ : FormalGroup.LawHom F H, κ.series = PowerSeries.subst θ.series η.series ∧
      PowerSeries.coeff 1 κ.series = PowerSeries.coeff 1 η.series * PowerSeries.coeff 1 θ.series := by sorry
