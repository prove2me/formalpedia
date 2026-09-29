-- Prove2me | Theorems.Thm_FormalGroup_exists_lawIso_series_eq_of_isUnit_coeff_one
-- name    : FormalGroup.exists_lawIso_series_eq_of_isUnit_coeff_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/05092d45-dcc7-50fe-9cad-49dabb3824bd
-- title:
--   Transport of a formal group law along an invertible series
-- statement:
--   Let $R$ be a commutative ring, let $F$ be a one-dimensional formal group law over $R$, and let $u \in R[[T]]$ be a power series whose constant coefficient vanishes and whose coefficient of $T$ is a unit of $R$. The assertion is that there is a formal group law $F'$ over $R$ with the following three properties. First, $u$ is the underlying series of an isomorphism $F \to F'$ in the sense of [`FormalGroup.LawIso`](def/FormalGroup_PointTransport.html#L24): that is, $u$ has zero constant coefficient, its linear coefficient is a unit, and the substitution identity $u(F(X,Y)) = F'(u(X), u(Y))$ holds, the left side being the substitution of the two-variable series $F$ into $u$ and the right side the substitution of $u(X)$ and $u(Y)$ into $F'$. Second, if $F$ is commutative then so is $F'$. Third, $F'$ is the only such law: every formal group law $F''$ over $R$ for which $u$ is the series of some isomorphism $F \to F''$ satisfies $F'' = F'$. Thus the conjugate law, informally $F'(X,Y) = u\bigl(F(u^{-1}X, u^{-1}Y)\bigr)$, exists, is unique, and inherits commutativity.
--
--   This is the transport-of-structure statement for one-dimensional formal group laws: an invertible change of parameter carries a law to a uniquely determined isomorphic law. It is used in the lifting step for formal groups over small extensions, and in comparing a Weierstrass curve's formal group with a law obtained over a quotient ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_lawIso_series_eq_of_isUnit_coeff_one.lean

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

theorem FormalGroup.exists_lawIso_series_eq_of_isUnit_coeff_one
    {R : Type u} [CommRing R] (F : FormalGroup R) (u : PowerSeries R)
    (hu0 : PowerSeries.constantCoeff u = 0) (hu1 : IsUnit (PowerSeries.coeff 1 u)) :
    ∃ F' : FormalGroup R, (∃ ψ : FormalGroup.LawIso F F', ψ.series = u) ∧ (F.IsComm → F'.IsComm) ∧
      ∀ F'' : FormalGroup R, (∃ ψ : FormalGroup.LawIso F F'', ψ.series = u) → F'' = F' := by sorry
