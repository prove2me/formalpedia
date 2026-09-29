-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_mem_range_d_zero_of_d_one_eq_zero_of_isAffine_of_basicOpen
-- name    : AlgebraicGeometry.OModulePresheaf.mem_range_d_zero_of_d_one_eq_zero_of_isAffine_of_basicOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/255389c9-f08c-51a5-bb4d-7674ae184d3b
-- title:
--   Čech H¹ of mathcal O_X vanishes on an affine scheme
-- statement:
--   Let $R$ be a commutative ring, let $X$ be an affine scheme and let $\pi \colon X \to \operatorname{Spec} R$ be a morphism of schemes. Let $\mathcal V$ be an ordered affine cover of $X$ in the sense of `Scheme.OrderedAffineCover`: a finite, linearly ordered index type $\iota$ together with opens $U_i \subseteq X$, each affine, whose supremum is all of $X$. Assume moreover that there are global sections $s_v \in \Gamma(X,\top)$, one for each $v \in \iota$, with $U_v = X_{s_v}$ the basic open set of $s_v$. Consider the $\mathcal O$-module presheaf `OModulePresheaf.unit π`, which assigns to an open $U$ the ring $\Gamma(X,U)$ viewed as an $R$-module through the algebra structure induced by $\pi$ and as a module over itself, with the presheaf restriction maps as transition maps. Let $z$ be a $1$-cochain for this presheaf on $\mathcal V$, that is, a family assigning to each index $\sigma$ of `𝒱.Idx 1` a section of $\mathcal O_X$ over the intersection $\bigcap_j U_{\sigma(j)}$ of the charts listed by $\sigma$, and suppose that $z$ is a cocycle, $d^1 z = 0$. The conclusion is that $z$ lies in the range of the $R$-linear differential $d^0$, i.e. $z$ is a coboundary.
--
--   This is the most elementary instance of Serre's vanishing theorem: the first Čech cohomology of the structure sheaf of an affine scheme with respect to a finite affine cover vanishes. It is used in the construction of a $0$-cochain solving a prescribed cocycle condition, in the form needed for the point-derivation statement [`AlgebraicGeometry.OModulePresheaf.exists_pointDerivations_d_zero_eq_of_d_one_eq_zero_of_isAffine_of_basicOpen`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_pointDerivations_d_zero_eq_of_d_one_eq_zero_of_isAffine_of_basicOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_mem_range_d_zero_of_d_one_eq_zero_of_isAffine_of_basicOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.mem_range_d_zero_of_d_one_eq_zero_of_isAffine_of_basicOpen
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X] (π : X ⟶ Spec (CommRingCat.of R))
    (𝒱 : X.OrderedAffineCover) (s : 𝒱.ι → Γ(X, ⊤)) (hs : ∀ v : 𝒱.ι, 𝒱.U v = X.basicOpen (s v))
    (z : (OModulePresheaf.unit π).cochain 𝒱 1) (hz : (OModulePresheaf.unit π).d 𝒱 1 z = 0) :
    z ∈ LinearMap.range ((OModulePresheaf.unit π).d 𝒱 0) := by sorry
