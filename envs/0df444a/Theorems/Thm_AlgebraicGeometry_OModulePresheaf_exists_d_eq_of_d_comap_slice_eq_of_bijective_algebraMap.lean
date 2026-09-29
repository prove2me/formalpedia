-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
-- name    : AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/4c1f8396-996b-59bd-90d0-4f286000a381
-- title:
--   Čech 1-cocycle on X×_k Y split by both slices
-- statement:
--   Let $k$ be a field and let $X$, $Y$, $P$ be schemes with morphisms $f_X : X \to \operatorname{Spec} k$ and $f_Y : Y \to \operatorname{Spec} k$ that are quasi-compact and separated, such that the composites $k \to \Gamma(X,\mathcal O_X)$ and $k \to \Gamma(Y,\mathcal O_Y)$ induced by $f_X$ and $f_Y$ on global sections (via the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism) are bijective. Assume given sections $x_0$ of $f_X$ and $y_0$ of $f_Y$, morphisms $p_1 : P \to X$, $p_2 : P \to Y$ forming a pullback square over $f_X$, $f_Y$, and closed immersions $i_X : X \to P$ with $i_X \, p_1 = \mathrm{id}_X$, $i_X \, p_2 = y_0 \circ f_X$, and $i_Y : Y \to P$ with $i_Y \, p_1 = x_0 \circ f_Y$, $i_Y \, p_2 = \mathrm{id}_Y$ (the two slices through $(x_0,y_0)$). Let $\mathcal W$ be an ordered affine cover of $P$: a finite linearly ordered index set $\iota$ together with affine opens $U_i \subseteq P$ whose supremum is $\top$. Let $c$ be a Čech $1$-cochain for the presheaf $U \mapsto \Gamma(P,U)$, regarded as a module over $k$ and over the sections via $p_1$ followed by $f_X$, i.e. a family of sections of $\mathcal O_P$ over the intersections indexed by $\mathcal W$ in degree $1$, with $d^1 c = 0$. Assume that the pullback of $c$ along $i_X$, obtained by applying $i_X$ on sections over each intersection and restricting to the corresponding intersection of the cover $i_X^{-1}\mathcal W$ (the cover of $X$ with the same index set and opens $i_X^{-1}U_i$), lies in the image of $d^0$ for the presheaf of sections of $\mathcal O_X$ over $k$ via $f_X$, and likewise for the pullback of $c$ along $i_Y$. Then $c$ lies in the image of $d^0$: there is a $0$-cochain $b$ for $\mathcal O_P$ on $\mathcal W$ with $d^0 b = c$.
--
--   This is the degree-one Künneth statement for the structure sheaf of a product of two $k$-schemes with $\Gamma = k$, in Čech form relative to a fixed ordered affine cover: a $1$-cocycle on $X\times_k Y$ whose restrictions to the slices $X\times\{y_0\}$ and $\{x_0\}\times Y$ are coboundaries is itself a coboundary. It is used in the obstruction-theoretic construction of group laws and lifts on relative Jacobians, being cited in the good-reduction arguments for relative group laws and for pullbacks of units along the two projections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (hY : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (y₀ : Spec (CommRingCat.of k) ⟶ Y) (hy₀ : y₀ ≫ fY = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iX : X ⟶ P) [IsClosedImmersion iX] (hiX₁ : iX ≫ p₁ = 𝟙 X) (hiX₂ : iX ≫ p₂ = fX ≫ y₀)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (hcX : ∃ b : (OModulePresheaf.unit fX).cochain (𝒲.comap iX) 0,
      (OModulePresheaf.unit fX).d (𝒲.comap iX) 0 b = fun s =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le iX s)).op).hom ((iX.app (𝒲.inter s)).hom (c s)))
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s))) :
    ∃ b : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 0, (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 0 b = c := by sorry
