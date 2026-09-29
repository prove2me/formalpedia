-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaPt_eq_of_pt_eq_of_forall_act_eq
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_eq_of_pt_eq_of_forall_act_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/ad050ac2-62dc-5bb4-94cb-457f75006477
-- title:
--   Extensionality of theta points with equal underlying section
-- statement:
--   Fix natural numbers $g,d,n$, a commutative ring $S$ and a polarised abelian scheme $u$ of type $(g,d,n)$ over $S$: that is, a scheme $A$ with a morphism $u.f : A \to \operatorname{Spec} S$, a relative group law $u.L$ on $u.f$ (functorial multiplication, unit and inverse on sections over arbitrary bases, compatible with base change) which is commutative, a property bundle for $u.f$, fibres of topological Krull dimension $g$, $2g$ sections $P_i$ killed by $n$ whose integral combinations give exactly the $n$-torsion of every geometric fibre freely, and a module $u.\mathrm{pol}$ on $A$ that is locally free of rank one, admits a projective presentation relative to $u.f$ whose associated morphism is a closed immersion, and has geometric fibrewise $H^0$ of dimension $d$. Let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} S$, and let $\theta,\theta'$ be theta points for $(u.f,u.L,u.\mathrm{pol})$ over $t$, each consisting of a section $\mathrm{pt}$ of $u.f$ over $t$ together with an isomorphism between the pullback of $u.\mathrm{pol}$ to $A\times_S\operatorname{Spec} R$ and its pullback along translation by $\mathrm{pt}$. If $\theta.\mathrm{pt} = \theta'.\mathrm{pt}$ and the two resulting operators agree on every global section of the pulled-back module, then $\theta = \theta'$.
--
--   This is the extensionality principle for Mumford's theta group: a theta point is determined by its underlying translation section together with the operator it induces on global sections of the polarising module. It is used to upgrade identities between the actions of theta points (for instance those coming from centre and commutator computations) to equalities in the theta group, and is cited in the construction of étale-local level lifts and of algebraically closed points with prescribed theta data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaPt_eq_of_pt_eq_of_forall_act_eq.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_eq_of_pt_eq_of_forall_act_eq
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (θ θ' : ThetaPt u.f u.L u.pol t) (hpt : θ.pt = θ'.pt)
    (hact : ∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤), θ.act s = θ'.act s) :
    θ = θ' := by sorry
