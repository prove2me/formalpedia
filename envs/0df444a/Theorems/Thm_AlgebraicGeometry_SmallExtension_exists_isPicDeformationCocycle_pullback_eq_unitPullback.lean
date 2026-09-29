-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_pullback_eq_unitPullback
-- name    : AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/934e7718-5e75-596a-87ab-e6815628ce21
-- title:
--   Pullback of a Picard deformation cocycle along a refinement
-- statement:
--   Let $B_1$ be a commutative ring, $k$ a field, and $V$ a module over both $k$ and $B_1$, equipped with a $B_1$-linear map $\iota : V \to B_1$ whose image is square-zero, i.e. $\iota(v)\iota(w)=0$ for all $v,w \in V$. Let there be given schemes $X,X',X_0,X_0',X_k,X_k'$, morphisms $f : X \to \operatorname{Spec} B_1$, $f' : X' \to \operatorname{Spec} B_1$, affine morphisms $g : X_0 \to X$, $g' : X_0' \to X'$, morphisms $f_k : X_k \to \operatorname{Spec} k$, $f_k' : X_k' \to \operatorname{Spec} k$, affine morphisms $i : X_k \to X$, $i' : X_k' \to X'$, and a morphism $h : X' \to X$ with $f' = f \circ h$, together with companions $h_0 : X_0' \to X_0$ satisfying $g \circ h_0 = h \circ g'$ and $h_k : X_k' \to X_k$ satisfying $i \circ h_k = h \circ i'$ and $f_k' = f_k \circ h_k$. Let $\mathcal U$ be an ordered affine cover of $X$ (a finite linearly ordered family of affine opens covering $X$) and $\mathcal W$ one of $X'$, with an index map $\lambda : \mathcal W.\iota \to \mathcal U.\iota$ such that $\mathcal W.U(w) \le h^{-1}\mathcal U.U(\lambda w)$ and, on the fibres, $i'^{-1}\mathcal W.U(w) \le h_k^{-1} i^{-1}\mathcal U.U(\lambda w)$. Finally let $M$ be an $\mathcal O_X$-module, $\varphi_0 : g^*M \cong \mathcal O_{X_0}$ an isomorphism onto the unit module, and $w$ a $k$-linear map from $\operatorname{Hom}_k(V,k)$ to the degree-one cochains of the unit $\mathcal O$-module presheaf of $f_k$ on the cover $i^{-1}\mathcal U$, and assume `IsPicDeformationCocycle` holds for $(V,\iota,f,f_k,i,g,\mathcal U,M,\varphi_0,w)$: there are a Čech trivialisation $\tau$ of $M$ on $\mathcal U$ (isomorphisms $M|_{\mathcal U.U(a)} \cong \mathcal O$) and sections $e(a), e'(a) \in \Gamma(X, \mathcal U.U(a))$ with $e(a)e'(a)=1$, such that $g^\sharp(e(a))$ is the unit-automorphism section measuring the discrepancy between the pullback of $\tau$ along $g$ and $\varphi_0$, and such that for each $1$-simplex $s$ the section $\tau.\mathrm{transition}(s)\cdot e'(s_0)|\cdot e(s_1)| - 1$ on $\mathcal U.\mathrm{inter}(s)$ admits a fibre reading by the $s$-component of $w$, i.e. equals $\sum_j \iota(v_j)s_j$ for finitely many $v_j \in V$, $s_j \in \Gamma$, with $w(\xi)_s = \sum_j \xi(v_j)\, i^\sharp(s_j)|$. Then there exists a $k$-linear $w'$ from $\operatorname{Hom}_k(V,k)$ to degree-one cochains of the unit presheaf of $f_k'$ on $i'^{-1}\mathcal W$ such that, first, $w'(\xi)$ is exactly the cochain pullback `OModulePresheaf.unitPullback` of $w(\xi)$ along $h_k$ through $\lambda$ (the signed restriction along the sorted $\lambda$-image of the simplex, zero when $\lambda$ is not injective on it), and second, $w'$ is again a Picard deformation cocycle, for $(V,\iota,f',f_k',i',g',\mathcal W)$, for the module $h^*M$, with the transported trivialisation $g'^*h^*M \cong h_0^*g^*M \cong h_0^*\mathcal O_{X_0} \cong \mathcal O_{X_0'}$ obtained by composing the comparison isomorphisms for iterated pullbacks, the isomorphism induced by $g \circ h_0 = h \circ g'$, the pullback of $\varphi_0$ along $h_0$ and the identification of $h_0^*$ of the unit module with the unit module.
--
--   This is the naturality, in degree one, of the Čech description of deformations of a line bundle along a square-zero thickening: a Picard deformation cocycle pulls back, with no flatness or cartesianness assumptions, to a Picard deformation cocycle for the pulled-back module on any refining cover. It is used in the study of line bundles on abelian schemes, where $h$ is instantiated at the slice maps $A \to A \times A$ and at inversion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isPicDeformationCocycle_pullback_eq_unitPullback.lean

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

theorem AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    (hJ : ∀ v w : V, ι v * ι w = 0)
    {X X' X₀ X₀' Xk Xk' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of B₁)) (f' : X' ⟶ Spec (CommRingCat.of B₁))
    (g : X₀ ⟶ X) [IsAffineHom g] (g' : X₀' ⟶ X') [IsAffineHom g']
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (fk' : Xk' ⟶ Spec (CommRingCat.of k))
    (i : Xk ⟶ X) [IsAffineHom i] (i' : Xk' ⟶ X') [IsAffineHom i']
    (h : X' ⟶ X) (hh : h ≫ f = f')
    (h₀ : X₀' ⟶ X₀) (hh₀ : h₀ ≫ g = g' ≫ h)
    (hk : Xk' ⟶ Xk) (hhk : hk ≫ i = i' ≫ h) (hfk : hk ≫ fk = fk')
    (𝒰 : X.OrderedAffineCover) (𝒲 : X'.OrderedAffineCover) (lam : 𝒲.ι → 𝒰.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒰.U (lam w))
    (hlamk : ∀ w, (𝒲.comap i').U w ≤ hk ⁻¹ᵁ (𝒰.comap i).U (lam w))
    (M : X.Modules) (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    ∃ w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').cochain (𝒲.comap i') 1,
      (∀ ξ : Module.Dual k V,
        w' ξ = OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 1 (w ξ)) ∧
      IsPicDeformationCocycle V ι f' fk' i' g' 𝒲 ((Scheme.Modules.pullback h).obj M)
        (((Scheme.Modules.pullbackComp g' h).app M) ≪≫
          ((Scheme.Modules.pullbackCongr hh₀.symm).app M) ≪≫
          ((Scheme.Modules.pullbackComp h₀ g).app M).symm ≪≫
          (Scheme.Modules.pullback h₀).mapIso φ₀ ≪≫
          Scheme.Modules.pullbackUnitIso h₀)
        w' := by sorry
