-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_HSucc_ofModules_tensorObj_tensorPow_linearEquiv_HSucc_tensor_twist_monoidalV2
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_HSucc_ofModules_tensorObj_tensorPow_linearEquiv_HSucc_tensor_twist_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/53ad0ee2-95db-5099-849a-854408f2c119
-- title:
--   Čech cohomology of FotimesL^{⊗ d} agrees with the twist datum
-- statement:
--   Let $A$ be a commutative ring, $X$ a scheme and $f : X \to \operatorname{Spec} A$. Let $\mathcal L$ be a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $\mathcal L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $N$ be a natural number and let $\mathfrak P$ be a `ProjPresentation` of $\mathcal L$ relative to $f$ of size $N$: it consists of global sections $\sigma_0,\dots,\sigma_N \in \Gamma(\mathcal L,\top)$, a morphism $\varphi = \mathfrak P.\mathrm{toProj} : X \to \operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $A$ with $\varphi$ followed by the structure morphism of $\mathbb P^N_A$ equal to $f$, the requirement that for each $i$ and each open $V$ contained in $\varphi^{-1}D_+(x_i)$ the map $g \mapsto g\cdot\sigma_i|_V$ from $\Gamma(X,V)$ to $\Gamma(\mathcal L,V)$ is bijective, and the requirement that on $\varphi^{-1}D_+(x_i)$ the pullback of the ratio $x_j/x_i$ carries $\sigma_i$ to $\sigma_j$. Assume $\varphi$ is an affine morphism. Let $\mathcal F$ be a sheaf of modules on $X$ whose associated module-presheaf datum `ofModules f 𝓕` (sections over opens, with their $\Gamma(X,U)$- and $A$-module structures and restriction maps) satisfies `IsQuasicoherent`: for every affine open $U$ and every $a \in \Gamma(X,U)$, each section over the basic open $X_a$ becomes, after multiplication by some power of $a$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $X_a$ is annihilated by some power of $a$. Then for all natural numbers $d$ and $i$ the type of $A$-linear equivalences between the $i$-th `HSucc`, that is $\ker d^{i+1}/\operatorname{im} d^{i}$, of the datum `ofModules f (𝓕 ⊗ 𝓛.tensorPow d)` and the $i$-th `HSucc` of the open-by-open tensor product of `ofModules f 𝓕` with the twist datum `ProjSpace.twist f 𝓅.toProj d`, both computed on the ordered affine cover of $X$ indexed by $\mathrm{Fin}(N+1)$ whose members are the preimages under $\varphi$ of the standard charts $D_+(x_j)$, is nonempty. Here $\mathcal L^{\otimes d}$ is formed by iterating the monoidal product, $\mathcal L^{\otimes 0}$ being the unit.
--
--   This is the comparison identifying the Čech cohomology, on the pulled-back standard cover of $\mathbb P^N_A$, of the monoidally formed sheaf $\mathcal F\otimes\mathcal L^{\otimes d}$ with that of the section-by-section twist of $\mathcal F$ by the frames description of $\varphi^*\mathcal O(d)$. It serves as the bridge between the sheaf-theoretic formulation of invertible modules and the frames-datum formulation in which the Serre vanishing machinery is set up, and is used in the proof of Serre vanishing for tensor powers of an invertible module along a finite projective presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_HSucc_ofModules_tensorObj_tensorPow_linearEquiv_HSucc_tensor_twist_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.nonempty_HSucc_ofModules_tensorObj_tensorPow_linearEquiv_HSucc_tensor_twist_monoidalV2
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (𝓛 : X.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (N : ℕ) (𝔓 : 𝓛.ProjPresentation f N) [IsAffineHom 𝔓.toProj]
    (𝓕 : X.Modules) (h𝓕 : (OModulePresheaf.ofModules f 𝓕).IsQuasicoherent) (d i : ℕ) :
    Nonempty ((OModulePresheaf.ofModules f (𝓕 ⊗ 𝓛.tensorPow d)).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i ≃ₗ[A]
      ((OModulePresheaf.ofModules f 𝓕).tensor (ProjSpace.twist f 𝔓.toProj d)).HSucc (ProjSpace.stdCoverPullback 𝔓.toProj) i) := by sorry
