-- Prove2me | Theorems.Thm_FormalGroup_evalSeries_map_algebraMap_eq_subst
-- name    : FormalGroup.evalSeries_map_algebraMap_eq_subst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/68d51f33-acd1-542e-860a-a8e54d463393
-- title:
--   Adic evaluation of a mapped power series is substitution
-- statement:
--   Let $T$ be a commutative ring in `Type` which is local, Noetherian and complete and separated for the adic topology of its maximal ideal (`IsAdicComplete (maximalIdeal T) T`). Let $g, s \in T[\![X]\!]$ be power series with $s$ of zero constant term. Equip $T[\![X]\!]$ with the `WithIdeal` structure given by its own maximal ideal $\mathfrak m =$ `maximalIdeal (PowerSeries T)`, so that $T[\![X]\!]$ carries the $\mathfrak m$-adic topology. Let $\tilde g$ be the power series with coefficients in $T[\![X]\!]$ obtained from $g$ by pushing each coefficient forward along the structure map $T \to T[\![X]\!]$, i.e. `PowerSeries.map (algebraMap T (PowerSeries T)) g`. Then the project's evaluation [`FormalGroup.evalSeries`](def/FormalGroup_NSeries.html#L85), which is `PowerSeries.eval₂ (algebraMap R A) x f` taken with the discrete uniformity on the coefficient ring, applied to $\tilde g$ at the point $s \in T[\![X]\!]$ — here the coefficient ring and the target ring are both $T[\![X]\!]$ and the algebra map is the identity, and the evaluation is the $\mathfrak m$-adic sum $\sum_n \tilde g_n s^n$ — coincides with the formal substitution `PowerSeries.subst s g`, the series $g(s)$.
--
--   This identifies the topological (adic) evaluation of a one-variable power series at a point with zero constant term with the purely formal substitution of power series, in the case where the ground ring is a power series ring over a complete Noetherian local ring. It is used in the treatment of the $n$-series of a formal group and of the origin chart of a Weierstrass curve, being cited by [`FormalGroup.linCombAdic_map_X_eq_nthSeries`](thm.html#FormalGroup.linCombAdic_map_X_eq_nthSeries) and by [`WeierstrassCurve.DrinfeldGlobal.exists_originChart_comp_schemeNsmul_eq_of_formalChart`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_originChart_comp_schemeNsmul_eq_of_formalChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_evalSeries_map_algebraMap_eq_subst.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem FormalGroup.evalSeries_map_algebraMap_eq_subst
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (g s : PowerSeries T) (hs : PowerSeries.constantCoeff s = 0) :
    (letI : WithIdeal (PowerSeries T) := ⟨maximalIdeal (PowerSeries T)⟩;
      FormalGroup.evalSeries (PowerSeries.map (algebraMap T (PowerSeries T)) g) s) = PowerSeries.subst s g := by sorry
