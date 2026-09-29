-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_eq_zero_of_forall_baseScalar_smul_eq_zero
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.eq_zero_of_forall_baseScalar_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/df25ee83-26b2-59d1-bee5-68d6d9bc330b
-- title:
--   Faithfulness of R on global sections of the pulled-back polarisation
-- statement:
--   Let $g,d,n$ be natural numbers, let $S$ be a commutative ring and let $u$ be a linearly polarised abelian scheme of these invariants over $S$: that is, a scheme $A$ with a morphism $f : A \to \operatorname{Spec} S$, a relative group law $L$ on $f$ (functorial group structure on $T$-points over $\operatorname{Spec} S$) that is commutative, the property bundle asserting $f$ smooth and proper with connected fibres and carrying a relative group law, fibres of topological Krull dimension $g$, a family $P_0,\dots,P_{2g-1}$ of $n$-torsion sections which on every geometrically algebraically closed fibre are independent and span the $n$-torsion, together with a module $\mathcal L$ on $A$ (the field `pol`) that is invertible (locally isomorphic to the unit module), satisfies `ClosedImmersionBySections` with respect to $f$, i.e. admits for some $N$ a projective presentation whose associated morphism to $\mathbb P^N$ is a closed immersion, and has geometric fibrewise $H^0$-rank $d$. Let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} S$ a morphism and $a \in R$. Write $\mathcal L_R$ for the pullback of $\mathcal L$ along the first projection of $A \times_{\operatorname{Spec} S} \operatorname{Spec} R$, and let $\mathrm{baseScalar}$ denote the image of $a$ in $\Gamma(A \times_S \operatorname{Spec} R, \mathcal O)$ obtained by pulling back along the second projection. If $\mathrm{baseScalar}(a) \cdot s = 0$ for every global section $s$ of $\mathcal L_R$, then $a = 0$.
--
--   The assertion is that the $R$-module of global sections of the pulled-back polarisation is faithful, so that a scalar recognised by its action on sections is determined; it is the input that lets scalars be read off from theta-type actions. It is used in the construction of the commutator pairing attached to the theta group action, namely by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_symmCocycle_forall_mul_act_eq_smul_act_of_forall_act_comm`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_symmCocycle_forall_mul_act_eq_smul_act_of_forall_act_comm) and [`AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_principalRoot_of_ne_zero`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_pt_eq_one_of_forall_act_comm_of_principalRoot_of_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_eq_zero_of_forall_baseScalar_smul_eq_zero.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.PolarisedAbelianScheme.eq_zero_of_forall_baseScalar_smul_eq_zero
    {g d n : ℕ} {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (a : R)
    (h : ∀ s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤), baseScalar u.f t a • s = 0) :
    a = 0 := by sorry
