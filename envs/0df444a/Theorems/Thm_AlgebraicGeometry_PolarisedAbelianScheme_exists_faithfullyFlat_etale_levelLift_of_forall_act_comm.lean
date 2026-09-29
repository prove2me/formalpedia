-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_levelLift_of_forall_act_comm
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_etale_levelLift_of_forall_act_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/1eceb5ed-3bab-5596-8851-c479da1c7edb
-- title:
--   Isotropic theta points lift homomorphically over an étale cover
-- statement:
--   Let $g,d,n$ be natural numbers, $S$ a commutative ring and $u$ a polarised abelian scheme of type $(g,d,n)$ over $S$: that is, a scheme $A$ with a structure morphism $u.f : A \to \operatorname{Spec} S$, a relative group law $u.L$ that is commutative, an abelian-scheme property bundle for $u.f$, fibres of topological Krull dimension $g$, a family of $2g$ sections of order dividing $n$ that is free and spanning on the $n$-torsion of every geometric fibre, and an invertible module $u.pol$ on $A$ whose sections give a closed immersion over $S$ and whose geometric fibrewise $H^0$ has rank $d$. Let $R$ be a commutative ring and $t : \operatorname{Spec} R \to \operatorname{Spec} S$, and let $K_1$ be a finite additive abelian group whose cardinality is invertible in $R$. Let $x : K_1 \to \{\varphi : \operatorname{Spec} R \to A \mid \varphi \circ u.f = t\}$ be a homomorphism for the group law $u.L$ on points over $t$, i.e. $x_0$ is the unit point and $x_{k+k'} = u.L.\mathrm{mul}\,(x_k)(x_{k'})$. Let $\theta^0 : K_1 \to \mathrm{ThetaPt}\ u.f\ u.L\ u.pol\ t$, so each $\theta^0_k$ consists of a point over $t$ together with an isomorphism between the pullback of the pullback of $u.pol$ to $A \times_S \operatorname{Spec} R$ along translation by that point and the pullback of $u.pol$ itself; assume the point of $\theta^0_k$ is $x_k$ for every $k$, and that the induced actions on global sections of the pullback of $u.pol$ to $A \times_S \operatorname{Spec} R$ commute pairwise: $\theta^0_k.\mathrm{act}(\theta^0_{k'}.\mathrm{act}\,s) = \theta^0_{k'}.\mathrm{act}(\theta^0_k.\mathrm{act}\,s)$ for all $k,k'$ and all $s$. Then there exists a commutative ring $R'$ with an $R$-algebra structure that is faithfully flat and étale over $R$, and a family $\mathrm{lift} : K_1 \to \mathrm{ThetaPt}\ u.f\ u.L\ u.pol\ (\operatorname{Spec}(R') \to \operatorname{Spec}(R) \xrightarrow{t} \operatorname{Spec} S)$ which is a homomorphism for the theta-point monoid structure ($\mathrm{lift}\,0 = 1$ and $\mathrm{lift}(k+k') = \mathrm{lift}\,k \cdot \mathrm{lift}\,k'$) and lies over the base change of $x$, in the sense that the underlying morphism of $\mathrm{lift}\,k$ is $\operatorname{Spec}$ of the structure map $R \to R'$ followed by the morphism underlying $x_k$.
--
--   This is the splitting of an isotropic (Lagrangian) finite subgroup of $R$-points into a level subgroup of the theta group, in the sense of Mumford's theory of theta groups of polarised abelian schemes: pairwise commuting theta points over a homomorphic family of points admit a genuinely multiplicative lift after a faithfully flat étale base change, the cover being needed to trivialise the resulting symmetric $2$-cocycle with values in $R^\times$. It is used in the construction of level structures on the theta group, namely by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_of_commutatorPairing_eq_pow`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_levelLifts_of_commutatorPairing_eq_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_faithfullyFlat_etale_levelLift_of_forall_act_comm.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_faithfullyFlat_etale_levelLift_of_forall_act_comm
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    {K₁ : Type} [AddCommGroup K₁] [Fintype K₁] (hK : IsUnit ((Fintype.card K₁ : ℕ) : R))
    (x : K₁ → SchemeHomOver t u.f) (hx0 : x 0 = u.L.one t) (hx : ∀ k k' : K₁, x (k + k') = u.L.mul t (x k) (x k'))
    (θ₀ : K₁ → ThetaPt u.f u.L u.pol t) (hθ₀ : ∀ k : K₁, (θ₀ k).pt = x k)
    (hcomm : ∀ (k k' : K₁) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)),
      (θ₀ k).act ((θ₀ k').act s) = (θ₀ k').act ((θ₀ k).act s)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R R'), Module.FaithfullyFlat R R' ∧ Algebra.Etale R R' ∧
      ∃ lift : K₁ → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ t),
        lift 0 = 1 ∧ (∀ k k' : K₁, lift (k + k') = lift k * lift k') ∧
        (∀ k : K₁, (lift k).pt.1 = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ (x k).1) := by sorry
