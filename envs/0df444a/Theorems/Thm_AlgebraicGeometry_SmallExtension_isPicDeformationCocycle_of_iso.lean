-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso
-- name    : AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/599aa3e5-9b07-50f4-b7b2-b682a97c5e92
-- title:
--   Picard deformation cocycles are invariant under isomorphism of modules
-- statement:
--   Let $B_1$ be a commutative ring, $k$ a field, $V$ a group carrying both a $k$-module and a $B_1$-module structure, and $\iota : V \to B_1$ a $B_1$-linear map. Let $f : X \to \operatorname{Spec} B_1$, $fk : X_k \to \operatorname{Spec} k$, an affine morphism $i : X_k \to X$, an affine morphism $g : X_0 \to X$ be given, together with an ordered affine cover $\mathcal U$ of $X$ (a finite, linearly ordered family of affine opens with supremum $\top$), sheaves of modules $M, M'$ on $X$, an isomorphism $e : M \cong M'$, an isomorphism $\varphi_0 : g^*M \cong \mathcal O_{X_0}$, and a $k$-linear map $w$ from the dual of $V$ to the $1$-cochains of the unit $\mathcal O$-module presheaf of $fk$ for the cover $i^{-1}\mathcal U$. Assume $\mathrm{IsPicDeformationCocycle}$ holds for $(V,\iota,f,fk,i,g,\mathcal U,M,\varphi_0,w)$: there are a Čech trivialisation $\tau_a : M|_{U_a} \cong \mathcal O_{U_a}$ and sections $e_a, e'_a \in \Gamma(X, U_a)$ with $e_a e'_a = 1$, such that $g^\sharp(e_a)$ is the unit-automorphism section comparing $g^*\tau_a$ with $\varphi_0$ on $g^{-1}U_a$, and for every $1$-simplex $s$ the section $\tau.\mathrm{transition}(s)\cdot e'_{s_0}|\cdot e_{s_1}| - 1$ on $U_s$ is a fibre reading, i.e. equals $\sum_j \iota(v_j)\, s_j$ for some $v_j \in V$, $s_j \in \Gamma(X,U_s)$ with $w(\xi)_s = \sum_j \xi(v_j)\, i^\sharp(s_j)|$ for all $\xi$. Then the same $w$ satisfies $\mathrm{IsPicDeformationCocycle}$ for $M'$ with the rigidification $g^*(e^{-1})$ followed by $\varphi_0$.
--
--   This is the invariance of the Picard deformation cocycle condition under replacing a rigidified module by an isomorphic one, the bookkeeping needed so that the cocycle attached to a deformation of a line bundle depends only on the isomorphism class of the rigidified pair. It is used in the construction of isomorphisms of abelian-scheme property bundles over small extensions, where deformations of invertible modules are compared through their Čech data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_iso
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g]
    (𝒰 : X.OrderedAffineCover)
    {M M' : X.Modules} (e : M ≅ M')
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M'
      ((Scheme.Modules.pullback g).mapIso e.symm ≪≫ φ₀) w := by sorry
