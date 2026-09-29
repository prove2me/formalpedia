-- Prove2me | Theorems.Thm_FormalGroup_LawIso_exists_symm_subst_eq_X
-- name    : FormalGroup.LawIso.exists_symm_subst_eq_X
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/d00cbde9-1a3a-5f91-a81a-ceedb84821ab
-- title:
--   Isomorphisms of formal group laws admit two-sided inverses
-- statement:
--   Let $R$ be a commutative ring and let $F$ and $G$ be one-dimensional formal group laws over $R$, i.e. terms of `FormalGroup R`, each given by a two-variable power series with vanishing constant coefficient. Let $\psi$ be a [`FormalGroup.LawIso F G`](def/FormalGroup_PointTransport.html#L24): a power series $\psi(X) \in R[[X]]$ with $\psi(0)=0$, satisfying the homomorphism identity $\psi(F(X_0,X_1)) = G(\psi(X_0),\psi(X_1))$ — in the Lean formulation, substituting the two-variable series of $F$ into $\psi$ agrees with substituting the pair $(\psi(X_0),\psi(X_1))$ into the series of $G$ — and such that the coefficient of $X$ in $\psi$ is a unit of $R$. The assertion is that there exists a [`FormalGroup.LawIso G F`](def/FormalGroup_PointTransport.html#L24), that is, a series $\psi'$ with $\psi'(0)=0$, unit linear coefficient and $\psi'(G(X_0,X_1)) = F(\psi'(X_0),\psi'(X_1))$, which is a two-sided substitutional inverse of $\psi$: substituting $\psi$ into $\psi'$ gives $X$, and substituting $\psi'$ into $\psi$ gives $X$.
--
--   This is the standard fact that an isomorphism of one-dimensional formal group laws is invertible in the category of formal group laws, so that `LawIso` is a genuine isomorphism notion and not merely a homomorphism with unit linear term. It is used throughout the formal-group material of the project, for instance in the transport of Drinfeld-type bases and trivialisations along isomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_LawIso_exists_symm_subst_eq_X.lean

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

theorem FormalGroup.LawIso.exists_symm_subst_eq_X
    {R : Type u} [CommRing R] {F G : FormalGroup R} (ψ : FormalGroup.LawIso F G) :
    ∃ ψ' : FormalGroup.LawIso G F,
      PowerSeries.subst ψ.series ψ'.series = PowerSeries.X ∧
        PowerSeries.subst ψ'.series ψ.series = PowerSeries.X := by sorry
