-- Prove2me | Theorems.Thm_FormalGroup_IsBaseChange_isComm
-- name    : FormalGroup.IsBaseChange.isComm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/8ed609f9-675a-5265-9ab2-613f293dd7b1
-- title:
--   Commutativity is preserved by base change of formal group laws
-- statement:
--   Let $R$ and $S$ be commutative rings, let $F$ be a one-dimensional formal group law over $R$, given by its underlying power series `F.toPowerSeries` in two variables, i.e. an element of `MvPowerSeries (Fin 2) R`, let $f : R \to S$ be a ring homomorphism, and let $G$ be a one-dimensional formal group law over $S$. Assume `F.IsBaseChange f G`, which by definition says that the power series of $G$ is obtained from that of $F$ by applying $f$ to each coefficient, $G_{\text{series}} =$ `MvPowerSeries.map f` $F_{\text{series}}$. Assume further that $F$ is commutative in the sense of the class `FormalGroup.IsComm`, whose content is the identity $F_{\text{series}} = F_{\text{series}}$ substituted along the assignment sending the variable $X_0$ to $X_1$ and $X_1$ to $X_0$, i.e. $F(X_0,X_1) = F(X_1,X_0)$. The conclusion is that $G$ is commutative in the same sense: $G_{\text{series}}$ equals its own substitution along the swap of the two variables, $G(X_0,X_1) = G(X_1,X_0)$.
--
--   This records that commutativity of a one-dimensional formal group law is inherited by its coefficientwise base change along a ring homomorphism. It is used to carry commutativity along the push-forwards occurring in the assembly of deformation rings for formal groups, for instance in the statements about Drinfeld bases and the universal deformation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsBaseChange_isComm.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsBaseChange.isComm
    {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) (f : R →+* S) (G : FormalGroup S)
    (h : F.IsBaseChange f G) [F.IsComm] : G.IsComm := by sorry
