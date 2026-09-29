-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom
-- name    : AlgebraicGeometry.Scheme.Hom.exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/3b16745a-1d60-510d-b7d2-e4cba8de586a
-- title:
--   Affine morphisms are relative spectra of their direct-image algebra
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe) and let $f : X \to Y$ be a morphism which is affine, i.e. satisfies `IsAffineHom`. Consider the natural transformation obtained by whiskering the comorphism $f.c$ of sheaves of rings along the opposite of `Scheme.AffineZariskiSite.toOpensFunctor Y`, the functor from the affine Zariski site of $Y$ (its affine opens) into the opens of $Y$; concretely this is the family of structure maps $\Gamma(U,\mathcal O_Y) \to \Gamma(X, f^{-1}U)$ indexed by the affine opens $U \subseteq Y$. The assertion is that there exists a proof $H$ that this natural transformation is coequifibered in the sense of Mathlib's `NatTrans.Coequifibered` — equivalently, for each affine open $U$ and each $r \in \Gamma(U,\mathcal O_Y)$ the ring $\Gamma(X, f^{-1}(D(r)))$ is the localisation of $\Gamma(X, f^{-1}U)$ away from the image of $r$ — and that there exists an isomorphism of schemes $e : X \cong$ the scheme glued from `Scheme.AffineZariskiSite.relativeGluingData H`, such that (i) $e$ followed by the structure morphism `toBase` of that gluing datum equals $f$, and (ii) for every affine open $U$ of $Y$, the open immersion $f^{-1}U \hookrightarrow X$ followed by $e$ equals the canonical morphism $f^{-1}U \to \operatorname{Spec}\Gamma(X, f^{-1}U)$ followed by the chart of the gluing indexed by $U$.
--
--   This is the standard identification of an affine morphism with the relative spectrum of its direct-image algebra, $X \cong \operatorname{Spec}_Y(f_*\mathcal O_X)$ over $Y$, in the form of a gluing datum over the affine Zariski site of $Y$, together with the compatibility of the isomorphism with the canonical charts over each affine open. It feeds the descent machinery for affine morphisms, being used by [`AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered`](thm.html#AlgebraicGeometry.exists_hom_glued_comp_toBase_eq_of_affHom_pushforwardUnit_of_coequifibered).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    ∃ (H : ((Scheme.AffineZariskiSite.toOpensFunctor Y).op.whiskerLeft f.c).Coequifibered)
      (e : X ≅ (Scheme.AffineZariskiSite.relativeGluingData H).glued),
      e.hom ≫ (Scheme.AffineZariskiSite.relativeGluingData H).toBase = f ∧
      ∀ U : Y.AffineZariskiSite, (f ⁻¹ᵁ U.1).ι ≫ e.hom =
        (f ⁻¹ᵁ U.1).toSpecΓ ≫ (Scheme.AffineZariskiSite.relativeGluingData H).cover.f U := by sorry
