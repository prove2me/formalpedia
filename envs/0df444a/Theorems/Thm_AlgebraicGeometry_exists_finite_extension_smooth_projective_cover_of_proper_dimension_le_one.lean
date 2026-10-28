-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_finite_extension_smooth_projective_cover_of_proper_dimension_le_one
-- name    : AlgebraicGeometry.exists_finite_extension_smooth_projective_cover_of_proper_dimension_le_one
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-24T19:54:42.684419+00:00
-- url     : https://prove2.me/theorems/549dc14e-93eb-467f-8710-7df999574585
-- title:
--   Smooth projective curve covers over a finite intermediate field, with dimension bound
-- statement:
--   Let $k$ be a field, let $K/k$ be an algebraic extension with $K$ algebraically closed, and let $C$ be a proper $k$-scheme of dimension at most one. There exist a finite intermediate field
--   $$k\subset E\subset K,$$
--   a smooth projective $E$-scheme $Y$ of dimension at most one, and a proper surjective morphism
--   $$f:Y\longrightarrow C.$$
--   If $p:Y\to\operatorname{Spec}E$ and $\pi:C\to\operatorname{Spec}k$ are the structure maps, then
--   $$\pi\circ f=(\operatorname{Spec}E\to\operatorname{Spec}k)\circ p.$$
--   Projectivity is exhibited by a closed immersion $j:Y\hookrightarrow\mathbb P^n_E$ with the given structure morphism $p$; properness of $p$ is also recorded.
--
--   The curve $C$ may be reducible, nonreduced, disconnected or empty, and $K/k$ may be infinite. The cover $Y$ is not required to be integral. This strengthens the finite smooth proper cover by retaining a projective embedding and the source dimension bound, providing finite-field curve-cover data for the alteration branch. **Formalization Note.** The field is an actual intermediate subfield of the prescribed $K$. No purely inseparable extension, canonical normalization, semistable family or smooth higher-dimensional total space is asserted.
-- source:
--   Derived from the Proved geometric-curve cover https://prove2.me/theorems/98944e77-2d0a-41a3-bad1-20bd6211e2e8 and relative field descent https://prove2.me/theorems/8113d2fc-8253-4a8a-a56e-405a6f283432 . The projective embedding is retained using the Proved projective-space base-change theorem https://prove2.me/theorems/b0c3d8f6-bffa-515d-a45a-3c3271585c3d and faithfully flat descent of closed immersions https://prove2.me/theorems/15a640ab-f9cc-514b-bd68-f574dde1accc . The relative descent argument is the algebraic-field-extension form of Stacks Project Lemma 32.10.1, https://stacks.math.columbia.edu/tag/01ZM . The dimension inequality is proved by lifting prime chains along faithfully flat maps using Mathlib going down and passing through stalk dimensions. This is a strengthened finite-field curve-cover input for the Philippon mission, not a proof of its remaining global alteration step.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_finite_extension_smooth_projective_cover_of_proper_dimension_le_one
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [IsAlgClosed K] {C : Scheme.{u}} (π : C ⟶ Spec (.of k)) [IsProper π]
    (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (Y : Scheme.{u}) (f : Y ⟶ C) (p : Y ⟶ Spec (.of E)),
      IsProper f ∧ Surjective f ∧ Smooth p ∧ IsProper p ∧
      topologicalKrullDim Y ≤ 1 ∧
      f ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      ∃ (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π E n = p := by sorry
