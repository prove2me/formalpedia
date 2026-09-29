-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_act_add_and_act_baseScalar_smul
-- name    : AlgebraicGeometry.Polarisation.ThetaPt.act_add_and_act_baseScalar_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/ab9db459-8399-52db-8c90-c6881840f3ac
-- title:
--   Additivity and base-scalar linearity of the theta action
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism, and $L$ a `RelativeGroupLaw` for $f$, i.e. a multiplication, unit and inverse on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-points over each $t : T \to \operatorname{Spec} S$, satisfying associativity, the unit laws, left inverses, and compatibility with precomposition in $T$. Let $\mathcal{L}$ be an object of `A.Modules`, let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} S$, and let $\theta$ be a theta point of $\mathcal{L}$ over $t$: a point `θ.pt` of $A$ over $t$ together with an isomorphism `θ.iso` from the pullback along the translation $\tau =$ `translate f L t θ.pt` of $\mathcal{L}_R :=$ (pullback of $\mathcal{L}$ along `pullback.fst f t`) to $\mathcal{L}_R$ itself. Write $U_\theta =$ `θ.act` for the resulting operator on $\Gamma(\mathcal{L}_R, \top)$, given by applying `θ.iso.hom` to the canonical image of a section under $\tau$. The conclusion is the conjunction of: $U_\theta(s + s') = U_\theta(s) + U_\theta(s')$ for all sections $s, s'$; and $U_\theta(c_r \cdot s) = c_r \cdot U_\theta(s)$ for all $r \in R$ and all $s$, where $c_r =$ `baseScalar f t r` $\in \Gamma(\mathrm{pullback}\ f\ t, \top)$ is the function obtained from $r$ by transporting along the $\Gamma$–$\operatorname{Spec}$ isomorphism and pulling back along `pullback.snd f t`. Linearity over arbitrary global functions on the base change is not asserted.
--
--   This records that the action of a theta point on global sections of the line bundle is $R$-linear, the basic compatibility underlying the theta group of a polarised abelian scheme in the sense of Mumford. It is used in the construction of Schrödinger frames and theta-adapted data for framed polarised abelian schemes, for instance in [`AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_isReframe_inter`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_isReframe_inter) and the accompanying idempotent decompositions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_ThetaPt_act_add_and_act_baseScalar_smul.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.Polarisation.ThetaPt.act_add_and_act_baseScalar_smul
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (θ : ThetaPt f L 𝓛 t) :
    (∀ s s' : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤), θ.act (s + s') = θ.act s + θ.act s') ∧
      ∀ (r : R) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)),
        θ.act (baseScalar f t r • s) = baseScalar f t r • θ.act s := by sorry
