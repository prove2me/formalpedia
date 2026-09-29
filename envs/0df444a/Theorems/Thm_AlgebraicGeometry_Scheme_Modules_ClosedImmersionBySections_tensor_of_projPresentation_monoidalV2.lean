-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_tensor_of_projPresentation_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.tensor_of_projPresentation_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/9ea35aaf-bc0d-58b4-9076-4e87c2011d81
-- title:
--   Closed immersion by sections tensored with a presented module
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} R$ a morphism, and $L, M$ two $\mathcal{O}_X$-modules (objects of `X.Modules`). Assume $L$ satisfies `ClosedImmersionBySections f`, that is: there are an $N$ and a `ProjPresentation` of $L$ over $f$ of size $N$ whose morphism `toProj` is a closed immersion; here a `ProjPresentation` of a module over $f$ of size $N$ consists of global sections $\sigma_0,\dots,\sigma_N$ of the module on $\top$, a morphism `toProj` from $X$ to $\operatorname{Proj}$ of the homogeneous subalgebra of $R[X_0,\dots,X_N]$ (i.e. $\mathbb{P}^N_R$) whose composite with the structure map `ProjSpace.π` is $f$, a frame condition asserting that for every $i$ and every open $V$ contained in the `toProj`-preimage of the basic open set of $X_i$ the map $g \mapsto g \cdot \sigma_i|_V$ from $\Gamma(X,V)$ to the module's sections on $V$ is bijective, and a ratio condition asserting that the pullback along `toProj` of the section $X_j/X_i$ of that basic open set carries $\sigma_i$ to $\sigma_j$ after restriction to its preimage. Assume moreover that $M$ carries some `ProjPresentation` over $f$ of size $N'$, with no condition on its morphism to $\mathbb{P}^{N'}_R$. Then the tensor product $L \otimes M$ satisfies `ClosedImmersionBySections f`.
--
--   This is the sections-theoretic form of the classical statement that the tensor product of a very ample sheaf with a globally generated (globally presented) one is again very ample, obtained via the Segre embedding of $\mathbb{P}^N_R \times_R \mathbb{P}^{N'}_R$. It is used in the computation of the rank of $H^0$ on geometric fibres for polarised abelian schemes with quaternionic multiplication, in [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.geomFibreH0Finrank_tensor_pullback_act_eq_natAbs_of_isAlgClosed`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.geomFibreH0Finrank_tensor_pullback_act_eq_natAbs_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_tensor_of_projPresentation_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.tensor_of_projPresentation_monoidalV2
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    {L M : X.Modules} (hL : L.ClosedImmersionBySections f) {N' : ℕ} (𝔓 : M.ProjPresentation f N') :
    (L ⊗ M).ClosedImmersionBySections f := by sorry
