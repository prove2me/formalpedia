-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_act_eq_smul_act_act
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_units_forall_thetaPt_act_act_eq_smul_act_act
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/c33989a9-08ee-5e1f-b3f4-ae03425610eb
-- title:
--   Theta points commute up to a unit of the base
-- statement:
--   Let $g,d,n$ be natural numbers, $S$ a commutative ring and $u$ a polarised abelian scheme of type $(g,d,n)$ over $S$: this packages a scheme $A$, a morphism $f\colon A\to\operatorname{Spec} S$, a relative group law $L$ on the functor of points of $f$ (a functorial group structure on sections $T\to A$ over $\operatorname{Spec} S$) which is commutative, a bundle of abelian-scheme properties for $f$, the requirement that every fibre of $f$ have topological Krull dimension $g$, a family $P_i$, $i\in\operatorname{Fin}(2g)$, of $n$-torsion sections that is independent and spans the $n$-torsion over every algebraically closed field, and a module $\mathrm{pol}$ on $A$ that is invertible, admits a projective presentation over $f$ whose associated morphism to projective space is a closed immersion, and has geometric fibrewise $H^0$-rank $d$. Let $R$ be a commutative ring, $t\colon\operatorname{Spec} R\to\operatorname{Spec} S$, and let $\theta,\theta'$ be theta points of $\mathrm{pol}$ over $t$, each consisting of a section $\mathrm{pt}$ of $f$ over $t$ together with an isomorphism between the pullback of $\mathrm{pol}_R$ along translation by $\mathrm{pt}$ and $\mathrm{pol}_R$, where $\mathrm{pol}_R$ denotes the pullback of $\mathrm{pol}$ along the first projection of $A\times_{\operatorname{Spec} S}\operatorname{Spec} R$. Then there is a unit $c\in R^\times$ such that for every global section $s$ of $\mathrm{pol}_R$ one has $\theta.\mathrm{act}(\theta'.\mathrm{act}\,s)=\mathrm{baseScalar}(c)\cdot\theta'.\mathrm{act}(\theta.\mathrm{act}\,s)$, where $\mathrm{act}$ is the action on sections obtained by pulling back along the translation and applying the given isomorphism, and $\mathrm{baseScalar}$ is the image of $c$ in $\Gamma(A\times_{\operatorname{Spec} S}\operatorname{Spec} R,\mathcal O)$ under the projection to $\operatorname{Spec} R$.
--
--   This is the commutator pairing $e_{\mathcal L}$ of the theta group, expressed through the action of theta points on global sections of the polarising module: two theta points commute up to multiplication by a unit of the base ring. It is used to extract the pairing itself and, further on, in the construction of complete orthogonal idempotents for the Schrödinger frame of a framed polarised abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_units_forall_thetaPt_act_act_eq_smul_act_act.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_units_forall_thetaPt_act_act_eq_smul_act_act
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (θ θ' : ThetaPt u.f u.L u.pol t) :
    ∃ c : Rˣ, ∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤),
      θ.act (θ'.act s) = baseScalar u.f t (c : R) • θ'.act (θ.act s) := by sorry
