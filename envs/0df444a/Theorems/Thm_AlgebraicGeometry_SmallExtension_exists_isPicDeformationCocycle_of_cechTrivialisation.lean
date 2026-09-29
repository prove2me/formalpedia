-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_of_cechTrivialisation
-- name    : AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_of_cechTrivialisation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/bbeb25aa-9bb3-566b-99e9-69981fa349d2
-- title:
--   Existence of a closed Picard deformation cocycle
-- statement:
--   Let $B_1$ be a local commutative ring with residue field $k = \mathrm{ResidueField}\,B_1$, let $B_0$ be a commutative ring and let $\pi \colon B_1 \to B_0$ be a surjective ring homomorphism whose kernel $J$ satisfies $J \cdot \mathfrak m_{B_1} = 0$ and $J \subseteq \mathfrak m_{B_1}$. Let $V$ be a finite-dimensional $k$-vector space which is also a $B_1$-module compatibly with the $k$-action, and let $\iota \colon V \to B_1$ be an injective $B_1$-linear map whose image is exactly $J$ viewed as a $B_1$-submodule. Let $f \colon X \to \operatorname{Spec} B_1$ be separated and flat, let $f_0 \colon X_0 \to \operatorname{Spec} B_0$ and an affine morphism $g \colon X_0 \to X$ form a pullback square over $\operatorname{Spec}\pi$, and let $f_k \colon X_k \to \operatorname{Spec} k$ and an affine morphism $i \colon X_k \to X$ form a pullback square over $\operatorname{Spec}$ of the residue map. Let $\mathcal U$ be an ordered affine cover of $X$ (a finite linearly ordered family of affine opens with supremum $\top$), $M$ an $\mathcal O_X$-module, $\tau$ a Čech trivialisation of $M$ on $\mathcal U$ (isomorphisms of each restriction of $M$ to $U_a$ with the unit module), and $\varphi_0 \colon g^*M \cong \mathcal O_{X_0}$. Then there is a $k$-linear map $w$ from the dual $V^\vee$ to the $1$-cochains of the unit $\mathcal O$-module presheaf of $f_k$ on the pulled-back cover $i^{-1}\mathcal U$ — that is, families of sections over the intersections $\bigcap_j i^{-1}U_{s(j)}$ — such that `IsPicDeformationCocycle` holds for $w$, i.e. there are a Čech trivialisation $\tau'$ of $M$ on $\mathcal U$ and sections $e_a, e'_a \in \Gamma(X, U_a)$ with $e_a e'_a = 1$, with $g^\sharp(e_a)$ equal to the section of the unit determined by the automorphism of $\mathcal O$ on $g^{-1}U_a$ obtained by conjugating $\varphi_0$ against $\tau'$ pulled back along $g$, and such that for every $1$-simplex $s$ the section $\tau'.\mathrm{transition}(s)\cdot e'_{s(0)}\cdot e_{s(1)} - 1$ on $U_{s(0)} \cap U_{s(1)}$ is fibre-read by $\xi \mapsto w(\xi)_s$: there are finitely many $v_j \in V$ and sections $s_j$ on that intersection with $\sum_j \iota(v_j)\, s_j$ equal to it and $w(\xi)_s = \sum_j \xi(v_j)\, i^\sharp(s_j)$ restricted to the corresponding open of $X_k$; moreover each $w(\xi)$ is a Čech cocycle, $d(w(\xi)) = 0$. Note that the conclusion asserts the existence of some Čech trivialisation in the sense above, not necessarily the given $\tau$.
--
--   This is the existence half of the deformation-theoretic description of invertible modules on a small (square-zero) thickening: an $\mathcal O_X$-module trivialised on the reduction modulo $J \cong V$ produces, after a choice of local trivialisations and of unit corrections, a closed Čech $1$-cocycle on $X_k$ with coefficients in $V^\vee$, whose class is the obstruction-theoretic invariant of the pair $(M, \varphi_0)$. It is used in the comparison of rigidified line bundles on abelian schemes and on fake elliptic curves over such thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_of_cechTrivialisation.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_of_cechTrivialisation
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π)
    (hsmall : RingHom.ker π * maximalIdeal B₁ = ⊥) (hI : RingHom.ker π ≤ maximalIdeal B₁)

    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker π))

    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [IsSeparated f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X) [IsAffineHom g]
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X) [IsAffineHom i]
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (𝒰 : X.OrderedAffineCover)
    (M : X.Modules) (τ : Scheme.Modules.CechTrivialisation 𝒰 M)
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf) :
    ∃ w : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1,
      IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w ∧
      ∀ ξ : Module.Dual (ResidueField B₁) V, (OModulePresheaf.unit fk).d (𝒰.comap i) 1 (w ξ) = 0 := by sorry
