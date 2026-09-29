-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id
-- name    : AlgebraicGeometry.OModulePresheaf.Leray.exists_dTot_eq_single_biAug_unitPullback_sub_single_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/9da3065c-6a27-5af4-accc-41798c7145f0
-- title:
--   Refinement pull-back and edge augmentations differ by a total coboundary
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $\pi\colon X\to\operatorname{Spec} R$ a morphism, and let $\mathfrak P,\mathcal W$ be ordered affine covers of $X$ (finite linearly ordered index sets together with affine opens whose supremum is $\top$). Let $\lambda\colon \mathcal W.\iota\to\mathfrak P.\iota$ satisfy $\mathcal W.U\,w\le (\mathbf 1_X)^{-1}(\mathfrak P.U\,\lambda w)$ for all $w$. Write $C^{a,b}=\prod_{\sigma,\tau}\Gamma(X,\ \mathcal W.\mathrm{inter}\,\tau\sqcap(\mathbf 1_X)^{-1}(\mathfrak P.\mathrm{inter}\,\sigma))$ for the bidegree-$(a,b)$ term of `LerayDblCpx (𝟙 X) π 𝔓 𝒲`, with total differential $d_H+(-1)^a d_V$ on $\mathrm{Tot}^n=\prod_{a+b=n}C^{a,b}$. Two assertions are made for cochains of the structure-sheaf datum `OModulePresheaf.unit (𝟙 X ≫ π)`. First, for every $\mathfrak P$-cochain $z$ in degree $0$ killed by the Čech differential, the augmentation `biAug` of the alternating refinement pull-back $\lambda^*z$ along $\mathbf 1_X$ equals, in bidegree $(0,0)$, the cochain $(\sigma,\tau)\mapsto z(\sigma)$ restricted from $\mathfrak P.\mathrm{inter}\,\sigma$ to $\mathcal W.\mathrm{inter}\,\tau\sqcap(\mathbf 1_X)^{-1}(\mathfrak P.\mathrm{inter}\,\sigma)$. Second, for every $n$ and every $\mathfrak P$-cocycle $z$ of degree $n+1$ there exists $h\in\mathrm{Tot}^n$ whose total coboundary is the element of $\mathrm{Tot}^{n+1}$ supported in the slot $(0,n+1)$ by `biAug` applied to $\lambda^*z$ minus the element supported in the slot $(n+1,0)$ by $(\sigma,\tau)\mapsto z(\sigma)$ restricted as above.
--
--   This is the homotopy comparing, in the Čech–Leray double complex attached to two ordered affine covers of one and the same scheme (the morphism being the identity), the two edge augmentations: the one coming from the refinement pull-back along $\lambda$ and the one coming from restriction of $\mathfrak P$-cochains. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated) to compare the Čech cohomology of the two covers, and hence towards independence of the cover for the structure sheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_dTot_eq_single_biAug_unitPullback_sub_single_id.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.Leray.exists_dTot_eq_single_biAug_unitPullback_sub_single_id
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (𝔓 𝒲 : X.OrderedAffineCover) (lam : 𝒲.ι → 𝔓.ι) (hlam : ∀ w, 𝒲.U w ≤ (𝟙 X) ⁻¹ᵁ 𝔓.U (lam w)) :
    (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 0)),
        OModulePresheaf.Leray.biAug (𝟙 X) π 𝔓 𝒲 0 (OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam 0 z.1) =
          (fun στ : OModulePresheaf.Leray.BiIdx 𝔓 𝒲 0 0 => (X.presheaf.map (homOfLE ((inf_le_right :
            OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 0 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans
              (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z.1 στ.1) :
            OModulePresheaf.Leray.biC (𝟙 X) π 𝔓 𝒲 0 0)) ∧
    ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (𝟙 X ≫ π)).d 𝔓 (n + 1)))),
      ∃ h : DoubleComplex.Tot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n,
        DoubleComplex.dTot (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲) n h =
          Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲).C i.1.1 i.1.2)
              ⟨(0, n + 1), by omega⟩
              (OModulePresheaf.Leray.biAug (𝟙 X) π 𝔓 𝒲 (n + 1)
                (OModulePresheaf.unitPullback (πX := 𝟙 X ≫ π) (𝟙 X) 𝒲 𝔓 lam hlam (n + 1) z.1)) -
            Pi.single (M := fun i : DoubleComplex.Diag (n + 1) => (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲).C i.1.1 i.1.2)
              ⟨(n + 1, 0), by omega⟩
              (fun στ : OModulePresheaf.Leray.BiIdx 𝔓 𝒲 (n + 1) 0 => (X.presheaf.map (homOfLE ((inf_le_right :
                OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 (n + 1) 0 στ.1 στ.2 ≤ (𝟙 X) ⁻¹ᵁ 𝔓.inter στ.1).trans
                  (Scheme.Hom.id_preimage (𝔓.inter στ.1)).le)).op).hom (z.1 στ.1)) := by sorry
