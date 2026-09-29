-- Prove2me | Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
-- name    : FormalGroup.LawHom.exists_isBaseChange_series_eq_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/4ee7beda-8b0d-5eb0-9af2-44970df23aff
-- title:
--   Base change of a homomorphism of formal group laws
-- statement:
--   Let $R$ and $S$ be commutative rings (in a common universe) and let $f : R \to S$ be a ring homomorphism. Let $F$ and $G$ be one-dimensional formal group laws over $R$, and let $\theta$ be a homomorphism from $F$ to $G$ in the sense of [`FormalGroup.LawHom`](def/FormalGroup_PointTransport.html#L15): a one-variable power series $\theta.\mathrm{series}$ over $R$ whose constant coefficient is $0$ and which satisfies the compatibility $\theta.\mathrm{series}\bigl(F(X_0,X_1)\bigr) = G\bigl(\theta.\mathrm{series}(X_0),\,\theta.\mathrm{series}(X_1)\bigr)$, the left-hand side being substitution of the two-variable series `F.toPowerSeries` into $\theta.\mathrm{series}$ and the right-hand side the substitution of the pair `LawHom.substX 0 θ.series`, `LawHom.substX 1 θ.series` (i.e. $\theta.\mathrm{series}$ with $X_i$ substituted for its variable) into `G.toPowerSeries`. Let further $F'$ and $G'$ be formal group laws over $S$ which are the base changes of $F$ and $G$ along $f$, in the sense that `F'.toPowerSeries` and `G'.toPowerSeries` are the coefficientwise images `MvPowerSeries.map f` of `F.toPowerSeries` and `G.toPowerSeries`. The conclusion is that there exists a homomorphism $\theta'$ from $F'$ to $G'$ whose underlying power series is exactly the coefficientwise image `PowerSeries.map f θ.series`.
--
--   This is the functoriality of homomorphisms of one-dimensional formal group laws under base change of the base ring: a homomorphism descends along $f$ to the base-changed laws, with the expected power series. It is used repeatedly in the study of Drinfeld bases and of lifts of formal groups, for instance in transporting a homomorphism to a trivial lift before composing with an inverse.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map.lean

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

theorem FormalGroup.LawHom.exists_isBaseChange_series_eq_map
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {F G : FormalGroup R}
    (θ : FormalGroup.LawHom F G) (F' G' : FormalGroup S)
    (hF : F.IsBaseChange f F') (hG : G.IsBaseChange f G') :
    ∃ θ' : FormalGroup.LawHom F' G', θ'.series = PowerSeries.map f θ.series := by sorry
