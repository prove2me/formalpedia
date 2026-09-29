-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero
-- name    : AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_unit_pullbackUnitIso_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/63ffa86b-4a0d-5da0-b5f9-14c9f121847a
-- title:
--   The unit line bundle is a zero Picard deformation cocycle
-- statement:
--   Let $B_1$ be a commutative ring, $k$ a field, and $V$ an abelian group carrying both a $k$-module and a $B_1$-module structure, together with a $B_1$-linear map $\iota : V \to B_1$. Let $X$, $X_0$, $X_k$ be schemes, $f : X \to \operatorname{Spec} B_1$ and $f_k : X_k \to \operatorname{Spec} k$ morphisms, $i : X_k \to X$ and $g : X_0 \to X$ affine morphisms, and let $\mathcal U$ be an ordered affine cover of $X$: a finite linearly ordered index type with affine opens $U_a$ whose supremum is $\top$. The assertion is that the structure sheaf $\mathcal O_X$ (the unit sheaf of modules on $X$), equipped with the canonical isomorphism $g^*\mathcal O_X \cong \mathcal O_{X_0}$ given by `Scheme.Modules.pullbackUnitIso g`, together with the zero $k$-linear map $V^\vee \to \check C^1(i^{-1}\mathcal U, \mathcal O_{X_k})$, satisfies `IsPicDeformationCocycle`. Unfolding that predicate, the conclusion is the existence of a Čech trivialisation $\tau$, i.e. isomorphisms $(U_a)^*\mathcal O_X \cong \mathcal O_{U_a}$ for all $a$, and of sections $e_a, e'_a \in \Gamma(X, U_a)$ with $e_a e'_a = 1$, such that: the image of $e_a$ under $g$ on $g^{-1}U_a$ equals the unit-automorphism section attached to the composite of $(\tau^{g})_a^{-1}$ with the restriction of `pullbackUnitIso g` to $g^{-1}U_a$; and for every $1$-index $s = (s_0 \le s_1)$ the section $\tau_{\text{trans}}(s)\,e'_{s_0}|\,e_{s_1}| - 1$ of $\mathcal O_X$ on $U_{s_0} \cap U_{s_1}$ is fibre-read by the $s$-component of the zero map, i.e. is a sum $\sum_j \iota(v_j)\,t_j$ with $v_j \in V$, $t_j \in \Gamma(X, U_{s_0}\cap U_{s_1})$ whose induced reading $\xi \mapsto \sum_j \xi(v_j)\,i^\sharp(t_j)|$ on $X_k$ is the prescribed (here zero) value.
--
--   This is the normalisation, or base point, of the Čech description of square-zero deformations of invertible sheaves: the trivial line bundle with its canonical trivialisation along $g$ carries the zero deformation class. It is used in the construction of isomorphisms of abelian schemes over a small extension, in [`GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_unit_pullbackUnitIso_zero.lean

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

theorem AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_unit_pullbackUnitIso_zero
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g] (𝒰 : X.OrderedAffineCover) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 (SheafOfModules.unit X.ringCatSheaf)
      (Scheme.Modules.pullbackUnitIso g) 0 := by sorry
