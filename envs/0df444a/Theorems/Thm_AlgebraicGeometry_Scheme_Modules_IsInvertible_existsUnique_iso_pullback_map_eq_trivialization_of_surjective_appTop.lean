-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_iso_pullback_map_eq_trivialization_of_surjective_appTop
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_iso_pullback_map_eq_trivialization_of_surjective_appTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/4387bbbf-a369-5ffe-81cc-3fc4ee6da8d4
-- title:
--   Unique ε-rigidified isomorphism of trivialised invertible modules
-- statement:
--   Let $B$, $A$, $Y$ be schemes, $e : B \to A$ and $\iota : Y \to A$ morphisms, $S'$ a commutative ring, and $f' : Y \to \operatorname{Spec} S'$ a morphism whose map on global sections $\Gamma(\operatorname{Spec} S', \top) \to \Gamma(Y, \top)$ is surjective. Assume given $\varepsilon : \operatorname{Spec} S' \to Y$ with $\varepsilon$ followed by $f'$ the identity, and $p : \operatorname{Spec} S' \to B$ with $\varepsilon$ followed by $\iota$ equal to $p$ followed by $e$. Let $L, M$ be modules on $A$, with $L$ invertible in the sense that every point of $A$ has an open neighbourhood $U$ for which the pullback of $L$ along the open immersion $U \to A$ is isomorphic to the unit module on $U$, and suppose given isomorphisms $hLe : e^*L \cong \mathcal O_B$ and $hMe : e^*M \cong \mathcal O_B$ (unit modules over the structure sheaf of rings of $B$). Assume finally that $\iota^*L$ and $\iota^*M$ are isomorphic at all. Then there is exactly one isomorphism $\varphi : \iota^*L \cong \iota^*M$ whose pullback $\varepsilon^*\varphi$ equals the canonical chain $\varepsilon^*\iota^*L \cong (\varepsilon\iota)^*L \cong (pe)^*L \cong p^*e^*L \cong p^*\mathcal O_B \cong \mathcal O_{\operatorname{Spec} S'}$, built from `Scheme.Modules.pullbackComp`, the transport along the equality of composites, $p^*hLe$ and `Scheme.Modules.pullbackUnitIso`, followed by the inverse of the corresponding chain for $M$ and $hMe$.
--
--   This is the existence and uniqueness of an isomorphism of invertible modules rigidified along a section, over a piece $Y$ of $A$ whose global functions all come from the affine base $\operatorname{Spec} S'$; it is the local step in the construction of rigidified line bundles for the relative Picard functor. It is used by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_locally_of_pullback_section_trivial`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_locally_of_pullback_section_trivial), which glues such rigidified isomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_iso_pullback_map_eq_trivialization_of_surjective_appTop.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_iso_pullback_map_eq_trivialization_of_surjective_appTop
    {B A Y : Scheme.{u}} (e : B ⟶ A) (ι : Y ⟶ A)
    (S' : Type u) [CommRing S'] (f' : Y ⟶ Spec (CommRingCat.of S'))
    (hΓ : Function.Surjective (f'.appTop).hom)
    (ε : Spec (CommRingCat.of S') ⟶ Y) (hε : ε ≫ f' = 𝟙 _)
    (p : Spec (CommRingCat.of S') ⟶ B) (hp : ε ≫ ι = p ≫ e)
    (L M : A.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hLe : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (hMe : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (h : Nonempty ((Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback ι).obj M)) :
    ∃! φ : (Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback ι).obj M,
      (Scheme.Modules.pullback ε).map φ.hom =
        ((Scheme.Modules.pullbackComp ε ι).app L ≪≫ (Scheme.Modules.pullbackCongr hp).app L ≪≫
            ((Scheme.Modules.pullbackComp p e).app L).symm ≪≫ (Scheme.Modules.pullback p).mapIso hLe ≪≫
            Scheme.Modules.pullbackUnitIso p).hom ≫
        ((Scheme.Modules.pullbackComp ε ι).app M ≪≫ (Scheme.Modules.pullbackCongr hp).app M ≪≫
            ((Scheme.Modules.pullbackComp p e).app M).symm ≪≫ (Scheme.Modules.pullback p).mapIso hMe ≪≫
            Scheme.Modules.pullbackUnitIso p).inv := by sorry
