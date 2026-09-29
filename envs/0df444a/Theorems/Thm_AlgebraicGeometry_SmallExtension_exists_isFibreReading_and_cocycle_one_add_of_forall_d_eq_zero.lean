-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isFibreReading_and_cocycle_one_add_of_forall_d_eq_zero
-- name    : AlgebraicGeometry.SmallExtension.exists_isFibreReading_and_cocycle_one_add_of_forall_d_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/33ea5e44-4740-5726-850a-d1f931f7acc0
-- title:
--   Unit cocycle 1+ε realising a closed Čech 1-cocycle of readings
-- statement:
--   Let $B_1$ be a local commutative ring, $B_0$ a commutative ring and $\pi \colon B_1 \to B_0$ a surjective ring homomorphism whose kernel satisfies $\ker\pi \cdot \mathfrak m_{B_1} = 0$ and $\ker\pi \subseteq \mathfrak m_{B_1}$. Let $V$ be a finite-dimensional vector space over the residue field $k$ of $B_1$, also a $B_1$-module compatibly with the residue map, and let $\iota \colon V \to B_1$ be an injective $B_1$-linear map whose image is exactly $\ker\pi$ (as a $B_1$-submodule). Let $f \colon X \to \operatorname{Spec} B_1$ be separated and flat, let $g \colon X_0 \to X$ be affine and exhibit $f_0 \colon X_0 \to \operatorname{Spec} B_0$ as the base change of $f$ along $\operatorname{Spec}\pi$, and let $i \colon X_k \to X$ be affine and exhibit $f_k \colon X_k \to \operatorname{Spec} k$ as the base change of $f$ along $\operatorname{Spec}$ of the residue map. Let $\mathcal U$ be an ordered affine cover of $X$, that is, a finite linearly ordered family of affine opens $U_a$ with $\bigsqcup_a U_a = X$, and let $\mathcal U$ pull back to the cover of $X_k$ by the opens $i^{-1}U_a$. Finally let $w \colon V^\vee \to \check C^1$ be $k$-linear into the degree-one Čech cochains of the structure presheaf of $X_k$ for that pulled-back cover, so $w(\xi)$ assigns to each strictly increasing pair $s$ a section of $\mathcal O_{X_k}$ on $\bigcap_j i^{-1}U_{s(j)}$, and assume $d\,w(\xi) = 0$ for every $\xi \in V^\vee$. Then there is a family of sections $\varepsilon_s \in \Gamma(X, \bigcap_j U_{s(j)})$, indexed by the strictly increasing pairs $s$, such that: (i) each $\varepsilon_s$ reads $\xi \mapsto w(\xi)_s$, i.e. there are $n$, elements $v_1,\dots,v_n \in V$ and sections $t_1,\dots,t_n$ over $\bigcap_j U_{s(j)}$ with $\sum_j \iota(v_j)\, t_j = \varepsilon_s$ (the scalars acting through the $B_1$-algebra structure induced by $f$) and $w(\xi)_s = \sum_j \xi(v_j)\, (i^\ast t_j)$ restricted to $\bigcap_j i^{-1}U_{s(j)}$ for all $\xi$; (ii) $(1+\varepsilon_s)(1-\varepsilon_s) = 1$; and (iii) for every strictly increasing triple $r$, the restrictions to $\bigcap_j U_{r(j)}$ satisfy $(1+\varepsilon_{\partial_2 r})(1+\varepsilon_{\partial_0 r}) = 1+\varepsilon_{\partial_1 r}$, where $\partial_j r$ denotes the $j$-th face of $r$.
--
--   This is the cocycle-realisation step in the Čech description of deformations of line bundles along a small extension $B_1 \to B_0$: a closed Čech $1$-cocycle with values in the conormal module $V^\vee$ is lifted to a cocycle of units $1+\varepsilon_s$ of $\mathcal O_X$ congruent to $1$ modulo $\ker\pi$, in the shape required for gluing a line bundle from local trivialisations. It is used by [`AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_of_forall_d_eq_zero`](thm.html#AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_of_forall_d_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isFibreReading_and_cocycle_one_add_of_forall_d_eq_zero.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.exists_isFibreReading_and_cocycle_one_add_of_forall_d_eq_zero
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
    (w : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : ∀ ξ : Module.Dual (ResidueField B₁) V, (OModulePresheaf.unit fk).d (𝒰.comap i) 1 (w ξ) = 0) :
    ∃ ε : ∀ s : 𝒰.Idx 1, Γ(X, 𝒰.inter s),
      (∀ s : 𝒰.Idx 1,
        IsFibreReading V ι f fk i (𝒰.inter s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s) (ε s)
          ((LinearMap.proj s).comp w)) ∧
      (∀ s : 𝒰.Idx 1, (1 + ε s) * (1 - ε s) = 1) ∧
      (∀ r : 𝒰.Idx 2,
        (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (1 + ε (𝒰.face r 2)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (1 + ε (𝒰.face r 0)) =
          (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (1 + ε (𝒰.face r 1))) := by sorry
