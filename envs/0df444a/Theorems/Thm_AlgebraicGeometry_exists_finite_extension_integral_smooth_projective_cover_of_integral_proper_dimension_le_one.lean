-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_finite_extension_integral_smooth_projective_cover_of_integral_proper_dimension_le_one
-- name    : AlgebraicGeometry.exists_finite_extension_integral_smooth_projective_cover_of_integral_proper_dimension_le_one
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-24T22:50:48.632335+00:00
-- url     : https://prove2.me/theorems/c413d547-014f-459d-aad9-d5914f26f9c0
-- title:
--   Geometrically integral smooth projective curve covers over a finite intermediate field
-- statement:
--   Let $k$ be a field, let $K/k$ be an algebraic extension with $K$ algebraically closed, and let $C$ be an integral proper $k$-scheme of dimension at most one. There exist a finite intermediate field
--   $$k\subset E\subset K,$$
--   a geometrically integral smooth projective $E$-scheme $Y$ of dimension at most one, and a proper surjective morphism
--   $$f:Y\longrightarrow C.$$
--   If $p:Y\to\operatorname{Spec}E$ and $\pi:C\to\operatorname{Spec}k$ are the structure morphisms, then
--   $$\pi\circ f=(\operatorname{Spec}E\to\operatorname{Spec}k)\circ p.$$
--   Projectivity is exhibited by a closed immersion $Y\hookrightarrow\mathbb P^n_E$ compatible with $p$. Properness, geometric integrality and geometric connectedness of $p$ are explicitly included.
--
--   The input curve need not be smooth, normal or geometrically integral, and $k$ may be imperfect. The algebraically closed algebraic extension may be infinite. The result retains geometric integrality as well as projectivity and dimension in the finite-field curve cover, supplying a geometrically connected source for subsequent alteration constructions. **Formalization Note.** The field is an actual intermediate subfield of the prescribed extension. The statement does not assert a purely inseparable extension, a canonical normalization or a semistable family.
-- source:
--   A strengthened finite-field curve-cover construction for the Philippon alteration branch. The geometric normalization and projectivity argument is the one checked in https://prove2.me/theorems/98944e77-2d0a-41a3-bad1-20bd6211e2e8 , with the integral proper-curve construction retained from its accepted source. The integral geometric curve is the reduced closure of a point over the original generic point. Its map to the original curve is universally closed by integrality; see Stacks Project, Section 29.45, https://stacks.math.columbia.edu/tag/01WG . The finite-field projective descent is the construction checked in https://prove2.me/theorems/549dc14e-93eb-467f-8710-7df999574585 , using the Proved relative descent https://prove2.me/theorems/8113d2fc-8253-4a8a-a56e-405a6f283432 and the filtered-limit principle of Stacks Project Lemma 32.10.1, https://stacks.math.columbia.edu/tag/01ZM . Integrality descent is proved directly from flat local stalk injections and topological irreducibility. This is not the remaining global alteration or semistable-reduction theorem.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_finite_extension_integral_smooth_projective_cover_of_integral_proper_dimension_le_one
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
    (π : C ⟶ Spec (.of k)) [IsProper π] (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (Y : Scheme.{u}) (f : Y ⟶ C) (p : Y ⟶ Spec (.of E)),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth p ∧ IsProper p ∧
      GeometricallyIntegral p ∧ GeometricallyConnected p ∧
      topologicalKrullDim Y ≤ 1 ∧
      f ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      ∃ (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π E n = p := by sorry
