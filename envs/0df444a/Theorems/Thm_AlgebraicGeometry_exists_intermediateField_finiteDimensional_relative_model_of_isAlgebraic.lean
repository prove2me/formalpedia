-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_relative_model_of_isAlgebraic
-- name    : AlgebraicGeometry.exists_intermediateField_finiteDimensional_relative_model_of_isAlgebraic
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-24T00:03:54.48671+00:00
-- url     : https://prove2.me/theorems/8113d2fc-8253-4a8a-a56e-405a6f283432
-- title:
--   A finite intermediate-field model retaining a morphism to a fixed scheme
-- statement:
--   Let $K/k$ be an algebraic field extension. Let $Y$ be a quasi-compact quasi-separated scheme locally of finite type over $k$, and let $X$ be a quasi-compact quasi-separated scheme locally of finite type over $K$. Suppose that a morphism
--   $$\varphi:X\longrightarrow Y$$
--   is compatible with their structure morphisms over $k$.
--
--   There are a finite intermediate extension $k\subset E\subset K$, a quasi-compact quasi-separated scheme $X_0$ locally of finite type over $E$, and morphisms
--   $$g:X\longrightarrow X_0,\qquad\varphi_0:X_0\longrightarrow Y$$
--   such that the square formed by $g$, the structure maps of $X$ and $X_0$, and $\operatorname{Spec}K\to\operatorname{Spec}E$ is cartesian. The map $\varphi_0$ is compatible with the $k$-structure of $Y$ and
--   $$\varphi_0\circ g=\varphi.$$
--   Thus the actual scheme and its given morphism both descend to one finite intermediate field.
--
--   The extension $K/k$ may be infinite, and neither scheme is required to be reduced, integral, connected, smooth or proper. **Formalization Note.** The statement is polymorphic in the common universe of the fields and schemes. It records an actual cartesian square and equality of morphisms, rather than only a coordinate-field bound. It does not assert descent of smoothness, properness or a projective embedding.
-- source:
--   Derived algebraic-field-extension form of Stacks Project, Lemma 32.10.1(1)-(2), https://stacks.math.columbia.edu/tag/01ZM , using the filtered union of finite intermediate fields and finite presentation over a field; the affine algebra input is the finite-presentation descent in Section 10.127, https://stacks.math.columbia.edu/tag/00QL . The implementation generalizes the accepted universe-zero constructions of the platform theorems https://prove2.me/theorems/55fe5d4b-b198-5f6d-9cfa-aca080243121 , https://prove2.me/theorems/053e91e1-cf68-5cc1-a30b-796cc221bea5 , https://prove2.me/theorems/f910075b-201e-550e-9756-da1c73c02076 and https://prove2.me/theorems/3bc798c4-6b03-5471-aee2-8579181005bf to arbitrary universes. The sole imported theorem is the already Proved universe-polymorphic algebra model https://prove2.me/theorems/6cbdde59-5710-5598-b9bf-4e962823ed98 . This supplies scheme and morphism descent infrastructure for geometric-generic-curve alteration, without asserting descent of the cover properties.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.exists_intermediateField_finiteDimensional_relative_model_of_isAlgebraic
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (Y : Scheme.{u}) (fY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace Y] [QuasiSeparatedSpace Y] [LocallyOfFiniteType fY]
    (X : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of K))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fX]
    (φ : X ⟶ Y)
    (hφ : φ ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of E))
      (_ : CompactSpace X₀) (_ : QuasiSeparatedSpace X₀) (_ : LocallyOfFiniteType f₀)
      (g : X ⟶ X₀) (φ₀ : X₀ ⟶ Y),
      IsPullback g fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap E K))) ∧
      φ₀ ≫ fY = f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      g ≫ φ₀ = φ := by sorry
