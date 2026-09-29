-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAlgClosed_factor_residueField_of_range_subset_singleton
-- name    : AlgebraicGeometry.Scheme.exists_isAlgClosed_factor_residueField_of_range_subset_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/79899e01-3982-5b97-9fca-3383086cd85d
-- title:
--   A common algebraically closed field for two field-valued points
-- statement:
--   Let $T$ be a scheme (in universe $u$) and $x$ a point of its underlying space. Let $k_1$ be a field (in universe $u$) and $s_1 \colon \operatorname{Spec} k_1 \to T$ a morphism of schemes whose underlying map has range contained in $\{x\}$, and likewise let $k_2$ be a field with $s_2 \colon \operatorname{Spec} k_2 \to T$ having range contained in $\{x\}$. The assertion is that there exist ring homomorphisms $\iota_1 \colon \kappa(x) \to k_1$ and $\iota_2 \colon \kappa(x) \to k_2$ out of the residue field `T.residueField x`, a type $\Omega$ in universe $u$ carrying a field structure and an algebraically closed field structure, and algebra structures $k_1 \to \Omega$ and $k_2 \to \Omega$, such that: $\operatorname{Spec} \iota_1$ followed by the canonical morphism `T.fromSpecResidueField x` equals $s_1$; $\operatorname{Spec} \iota_2$ followed by that same morphism equals $s_2$; the two composites $\kappa(x) \to k_i \to \Omega$ obtained from $\iota_i$ and the structure maps $\operatorname{algebraMap} k_i \Omega$ agree; and, correspondingly on spectra, $\operatorname{Spec}(\operatorname{algebraMap} k_1 \Omega)$ followed by $s_1$ equals $\operatorname{Spec}(\operatorname{algebraMap} k_2 \Omega)$ followed by $s_2$.
--
--   This is the standard fact that a morphism from the spectrum of a field into a scheme supported at $x$ factors through $\operatorname{Spec} \kappa(x)$, together with the existence of a common algebraically closed over-field of two such field-valued points at the same $x$. It is used to compare properties of geometric fibres of a family at two geometric points lying over one point of the base, by base change up to $\Omega$; it is cited in the relative Picard development for the point-independence statements [`AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations`](thm.html#AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoGluedSmoothCurveDegenerations) and [`AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoLineDegenerations`](thm.html#AlgebraicGeometry.RelPicard.isAlgEquivZero_fibre_of_range_subset_singleton_of_twoLineDegenerations).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isAlgClosed_factor_residueField_of_range_subset_singleton.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_isAlgClosed_factor_residueField_of_range_subset_singleton
    {T : Scheme.{u}} (x : T)
    {k₁ : Type u} [Field k₁] (s₁ : Spec (CommRingCat.of k₁) ⟶ T) (hs₁ : Set.range ⇑s₁ ⊆ {x})
    {k₂ : Type u} [Field k₂] (s₂ : Spec (CommRingCat.of k₂) ⟶ T) (hs₂ : Set.range ⇑s₂ ⊆ {x}) :
    ∃ (ι₁ : T.residueField x ⟶ CommRingCat.of k₁) (ι₂ : T.residueField x ⟶ CommRingCat.of k₂)
      (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k₁ Ω) (_ : Algebra k₂ Ω),
      Spec.map ι₁ ≫ T.fromSpecResidueField x = s₁ ∧
      Spec.map ι₂ ≫ T.fromSpecResidueField x = s₂ ∧
      ι₁ ≫ CommRingCat.ofHom (algebraMap k₁ Ω) = ι₂ ≫ CommRingCat.ofHom (algebraMap k₂ Ω) ∧
      Spec.map (CommRingCat.ofHom (algebraMap k₁ Ω)) ≫ s₁ =
        Spec.map (CommRingCat.ofHom (algebraMap k₂ Ω)) ≫ s₂ := by sorry
