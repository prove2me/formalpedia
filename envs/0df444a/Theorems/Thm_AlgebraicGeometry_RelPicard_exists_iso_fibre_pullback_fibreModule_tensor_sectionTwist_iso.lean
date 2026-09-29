-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso
-- name    : AlgebraicGeometry.RelPicard.exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/8842df3c-cc47-5c08-a960-cef56a2a6b00
-- title:
--   Fibre over a rational point identifies with C, compatibly with theta twists
-- statement:
--   Let $k$ be a field, let $C$ and $T$ be schemes, and let $c : C \to \operatorname{Spec} k$ be proper and smooth of relative dimension $1$. Let $\varepsilon$ be a $k$-point of $C$, i.e. a morphism $\varepsilon_1 : \operatorname{Spec} k \to C$ together with a proof that $\varepsilon_1$ followed by $c$ is the identity; let $t : T \to \operatorname{Spec} k$ be a morphism and $x : \operatorname{Spec} k \to T$ a section of it, so $x$ followed by $t$ is the identity. Write $i_x :=$ `pullback.lift (𝟙 C) (c ≫ x)` $: C \to C \times_k T$ for the morphism with components $\mathrm{id}_C$ and $c$ followed by $x$. The assertion is that there exists an isomorphism of schemes $\varphi : C \cong (C \times_k T) \times_T \operatorname{Spec} k$, the target being the pullback of `pullback.snd c t` along $x$, such that: (i) $\varphi$ followed by `fibreAt c t x`, the second projection of that pullback, equals $c$; (ii) $\varphi$ followed by the first projection to $C \times_k T$ equals $i_x$; and (iii) for every object $F$ of the category of modules on $C \times_k T$ and every natural number $d$, the pullback along $\varphi$ of the restriction of $F \otimes$ `sectionTwist c ε t d` to the fibre — where `sectionTwist c ε t d` is the dual (internal hom into the unit) of the ideal-sheaf module of the $d$-th power of the kernel ideal sheaf of `rigSection c t ε`, and the restriction is pullback along the first projection — is isomorphic to the pullback of $F$ along $i_x$ tensored with the dual of the ideal-sheaf module of the $d$-th power of the kernel ideal sheaf of $\varepsilon_1$ on $C$. The isomorphism in (iii) is asserted only as a nonempty type of isomorphisms, and no compatibility between the isomorphisms for varying $F$ and $d$ is claimed.
--
--   This is the base-change statement identifying the fibre of $C \times_k T \to T$ over a rational point $x$ of $T$ with $C$ itself, together with the compatibility of the theta-type twisting sheaves: the relative divisor attached to the section induced by $\varepsilon$ restricts on the fibre to the divisor $d\varepsilon$ on $C$. It is used in the analysis of the relative Picard functor, where the statement on points and the vanishing criterion for $H^0$ is deduced by comparing the relative construction with its fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_iso_fibre_pullback_fibreModule_tensor_sectionTwist_iso
    {k : Type u} [Field k] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (t : T ⟶ Spec (CommRingCat.of k))
    (x : Spec (CommRingCat.of k) ⟶ T) (hx : x ≫ t = 𝟙 _) :
    ∃ φ : C ≅ pullback (pullback.snd c t) x,
      φ.hom ≫ fibreAt c t x = c ∧
      φ.hom ≫ pullback.fst (pullback.snd c t) x =
        pullback.lift (𝟙 C) (c ≫ x) (by rw [Category.id_comp, Category.assoc, hx, Category.comp_id]) ∧
      ∀ (F : (pullback c t).Modules) (d : ℕ),
        Nonempty ((Scheme.Modules.pullback φ.hom).obj (fibreModule c t x (F ⊗ sectionTwist c ε t d)) ≅
          (Scheme.Modules.pullback
              (pullback.lift (𝟙 C) (c ≫ x) (by rw [Category.id_comp, Category.assoc, hx, Category.comp_id]))).obj F ⊗
            ((ε.1.ker) ^ d).invModule) := by sorry
