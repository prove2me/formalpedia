-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentCharacter_exists_isInvertible_iso_comp_eq_of_cocycle
-- name    : AlgebraicGeometry.DescentCharacter.exists_isInvertible_iso_comp_eq_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/19353a6f-828a-55a8-8151-bc18a8a125b0
-- title:
--   Effectivity of descent data for invertible modules along affine faithfully flat maps
-- statement:
--   Let $q\colon X\to Y$ be a morphism of schemes that is affine, flat and surjective. Let $p_1,p_2\colon P\to X$ exhibit $P$ as a pullback of $q$ along $q$ (so $P$ plays the role of $X\times_Y X$), let $\delta\colon X\to P$ satisfy $\delta\ \text{followed by}\ p_1=\mathrm{id}_X$ and $\delta\ \text{followed by}\ p_2=\mathrm{id}_X$, let $a,b\colon P_3\to P$ exhibit $P_3$ as a pullback of $p_2$ along $p_1$ (the role of $X\times_YX\times_YX$), and let $c\colon P_3\to P$ satisfy $c\ \text{followed by}\ p_1=a\ \text{followed by}\ p_1$ and $c\ \text{followed by}\ p_2=b\ \text{followed by}\ p_2$. Let $M$ be a module on $Y$ which is invertible in the sense that every point of $Y$ has an open neighbourhood $U$ on which the pullback of $M$ along the inclusion $U\hookrightarrow Y$ is isomorphic to the unit sheaf of modules of $U$, and let $\varphi\colon p_1^*q^*M\to p_2^*q^*M$ be a morphism of modules on $P$. Assume the unit condition: pulling $\varphi$ back along $\delta$ and transporting it by the canonical comparisons $\delta^*p_i^*\cong(\delta\ \text{followed by}\ p_i)^*$ and by the equalities $\delta\ \text{followed by}\ p_i=\mathrm{id}_X$ gives the identity of $q^*M$. Assume the cocycle condition: the composite of the transport of $\varphi$ along $a$ with the transport of $\varphi$ along $b$ (matched by the equality $a\ \text{followed by}\ p_2=b\ \text{followed by}\ p_1$) equals the transport of $\varphi$ along $c$, using the equalities $c\ \text{followed by}\ p_1=a\ \text{followed by}\ p_1$ and $c\ \text{followed by}\ p_2=b\ \text{followed by}\ p_2$. Then there exist a module $N$ on $Y$, invertible in the same sense, and an isomorphism $\beta\colon q^*N\cong q^*M$ such that $p_1^*\beta$ followed by $\varphi$ equals the canonical identification $p_1^*q^*N\cong(p_1\ \text{followed by}\ q)^*N=(p_2\ \text{followed by}\ q)^*N\cong p_2^*q^*N$ (the latter equality coming from the commutativity of the pullback square) followed by $p_2^*\beta$.
--
--   This is the effectivity half of faithfully flat descent for invertible modules, in the concrete kernel-pair formulation: a gluing morphism on $X\times_YX$ satisfying the unit and cocycle conditions arises from an invertible module on $Y$ together with an isomorphism of its pullback with $q^*M$. It is obtained from the effectivity of descent data for the pseudofunctor of modules along an affine flat surjection, and is used in the construction of invertible modules with prescribed descent character, in particular in the polarisation result [`AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_pullback_schemeNsmul_two_trivial_hasValue_translate`](thm.html#AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_pullback_schemeNsmul_two_trivial_hasValue_translate).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentCharacter_exists_isInvertible_iso_comp_eq_of_cocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.exists_isInvertible_iso_comp_eq_of_cocycle
    {X Y P P₃ : Scheme.{u}} (q : X ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (p₁ p₂ : P ⟶ X) (hP : IsPullback p₁ p₂ q q)
    (δ : X ⟶ P) (hδ₁ : δ ≫ p₁ = 𝟙 X) (hδ₂ : δ ≫ p₂ = 𝟙 X)
    (a b : P₃ ⟶ P) (hP₃ : IsPullback a b p₂ p₁) (c : P₃ ⟶ P) (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂)
    {M : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (φ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₂).obj ((Scheme.Modules.pullback q).obj M))
    (hunit :
      (Scheme.Modules.pullbackCongr hδ₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp δ p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback δ).map φ ≫
            (Scheme.Modules.pullbackComp δ p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hδ₂).hom.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _)
    (hcocycle :
      ((Scheme.Modules.pullbackComp a p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback a).map φ ≫
          (Scheme.Modules.pullbackComp a p₂).hom.app ((Scheme.Modules.pullback q).obj M)) ≫
      ((Scheme.Modules.pullbackCongr hP₃.w).hom.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp b p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback b).map φ ≫
            (Scheme.Modules.pullbackComp b p₂).hom.app ((Scheme.Modules.pullback q).obj M)) =
      (Scheme.Modules.pullbackCongr hca).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp c p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback c).map φ ≫
            (Scheme.Modules.pullbackComp c p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hcb).hom.app ((Scheme.Modules.pullback q).obj M)) :
    ∃ (N : Y.Modules) (_ : Scheme.Modules.IsInvertible N)
      (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M),
      (Scheme.Modules.pullback p₁).map β.hom ≫ φ =
        ((Scheme.Modules.pullbackComp p₁ q).hom.app N ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj N = (Scheme.Modules.pullback (p₂ ≫ q)).obj N by
            rw [hP.w]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app N) ≫ (Scheme.Modules.pullback p₂).map β.hom := by sorry
