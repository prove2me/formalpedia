-- Prove2me | Theorems.Thm_FormalGroup_linCombAdic_map_X_eq_nthSeries
-- name    : FormalGroup.linCombAdic_map_X_eq_nthSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/de6c6eff-b3c0-5e7b-96a9-5c0d4f3ed911
-- title:
--   Adic linear combination at (q,0) is the q-series
-- statement:
--   Let $T$ be a commutative local Noetherian ring which is complete and separated for the adic topology of its maximal ideal $\mathfrak m$, let $F$ be a formal group law over $T$, let $q$ be a natural number, and let $w \in T[[X]]$ lie in the maximal ideal of the local ring `PowerSeries T`. Form the formal group $F.map(\mathrm{algebraMap}\,T\,T[[X]])$ over $T[[X]]$ obtained from $F$ by functoriality along the inclusion of constants $T \to T[[X]]$, and evaluate its $\mathfrak m_{T[[X]]}$-adic linear combination `linCombAdic` at the arguments $x_0 =$ `PowerSeries.X`, $x_1 = w$ and multipliers $a = q$, $b = 0$; by definition this is the value of the group law of the base-changed formal group, evaluated adically, at the pair consisting of the $q$-fold adic sum of $X$ with itself and the $0$-fold adic sum of $w$ with itself. The assertion is that this element of $T[[X]]$ equals $F$'s $q$-th series `F.nthSeries q`, that is $[q]_F$, defined by $[0]_F = 0$ and $[n+1]_F = F([n]_F(X), X)$. In particular the value does not depend on $w$.
--
--   This identifies the $\mathfrak m$-adic linear combination of the tautological parameter with multipliers $(q,0)$ as the multiplication-by-$q$ series of the formal group, the formal-group counterpart of $q$-fold addition. It is used in [`WeierstrassCurve.DrinfeldGlobal.exists_originChart_comp_schemeNsmul_eq_of_formalChart`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_originChart_comp_schemeNsmul_eq_of_formalChart) to match the scheme-theoretic $q$-fold sum on a Weierstrass curve with the formal group law read through the chart at the origin.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_linCombAdic_map_X_eq_nthSeries.lean

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

theorem FormalGroup.linCombAdic_map_X_eq_nthSeries
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (F : FormalGroup T) (q : ℕ) (w : PowerSeries T) (hw : w ∈ maximalIdeal (PowerSeries T)) :
    (F.map (algebraMap T (PowerSeries T))).linCombAdic (maximalIdeal (PowerSeries T)) PowerSeries.X w q 0 =
      F.nthSeries q := by sorry
