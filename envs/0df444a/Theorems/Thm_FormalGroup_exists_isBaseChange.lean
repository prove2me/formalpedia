-- Prove2me | Theorems.Thm_FormalGroup_exists_isBaseChange
-- name    : FormalGroup.exists_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/ab1160fe-917d-5b1a-8836-c070ce30fb45
-- title:
--   Base change of a formal group law along a ring map
-- statement:
--   Let $R$ and $S$ be commutative rings, let $F$ be a one-dimensional formal group law over $R$ (a `FormalGroup R`, whose underlying datum is the bivariate power series `F.toPowerSeries` in `MvPowerSeries (Fin 2) R` subject to the group-law axioms), and let $f : R \to S$ be a ring homomorphism. The assertion is that there exists a one-dimensional formal group law $G$ over $S$ such that `F.IsBaseChange f G` holds, which by definition means that the underlying power series of $G$ is the coefficientwise image of that of $F$, that is $G.\mathrm{toPowerSeries} = \mathrm{MvPowerSeries.map}\ f\ (F.\mathrm{toPowerSeries})$. In other words, applying $f$ to each coefficient of $F(X_0,X_1)$ again yields a formal group law over $S$, and the existence statement packages that series together with the verification of the group-law axioms over $S$. No hypotheses beyond commutativity of the two rings are imposed; in particular neither ring need be local, noetherian, or of positive characteristic.
--
--   This is the existence half of base change (extension of scalars) for one-dimensional formal group laws: the formal group law $f_*F$ over $S$ obtained by pushing the coefficients of $F$ forward along $f$. It is used to produce base-changed laws together with the `IsBaseChange` relation, and is cited in the analysis of Drinfeld bases, namely in [`FormalGroup.IsDrinfeldBasisAdic.maximalIdeal_eq_span_pair_of_universal_of_isComm`](thm.html#FormalGroup.IsDrinfeldBasisAdic.maximalIdeal_eq_span_pair_of_universal_of_isComm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_isBaseChange.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.exists_isBaseChange
    {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) (f : R →+* S) :
    ∃ G : FormalGroup S, F.IsBaseChange f G := by sorry
