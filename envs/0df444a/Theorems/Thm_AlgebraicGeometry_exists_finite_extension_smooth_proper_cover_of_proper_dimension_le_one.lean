-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_finite_extension_smooth_proper_cover_of_proper_dimension_le_one
-- name    : AlgebraicGeometry.exists_finite_extension_smooth_proper_cover_of_proper_dimension_le_one
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-24T01:09:42.689684+00:00
-- url     : https://prove2.me/theorems/23631471-09be-491d-888c-22e5abe84a47
-- title:
--   Smooth proper curve covers over a finite intermediate extension
-- statement:
--   Let $k$ be a field, let $K/k$ be an algebraic extension with $K$ algebraically closed, and let $C$ be a proper $k$-scheme of dimension at most one. There exist a finite intermediate extension
--   $$k\subset E\subset K,$$
--   a smooth proper $E$-scheme $Y$, and a proper surjective morphism
--   $$f:Y\longrightarrow C$$
--   compatible with the displayed field extension: if $p:Y\to\operatorname{Spec}E$ and $\pi:C\to\operatorname{Spec}k$ are the structure maps, then
--   $$\pi\circ f=(\operatorname{Spec}E\to\operatorname{Spec}k)\circ p.$$
--
--   This gives a finite-field smooth proper cover of the original curve, including reducible, nonreduced and empty proper curves. The chosen algebraically closed extension may be infinite. The assertion does not require the cover to be integral and does not assert a projective embedding or a dimension bound for its source. **Formalization Note.** The finite field is exhibited as an intermediate subfield of $K$, and the scalar compatibility is an equality of scheme morphisms.
-- source:
--   Derived from the Proved geometric-curve cover https://prove2.me/theorems/98944e77-2d0a-41a3-bad1-20bd6211e2e8 and the Proved universe-polymorphic relative field descent https://prove2.me/theorems/8113d2fc-8253-4a8a-a56e-405a6f283432 . Descent of a finite-presentation scheme and its map is the algebraic-extension form of Stacks Project Lemma 32.10.1, https://stacks.math.columbia.edu/tag/01ZM . Smoothness and universal closedness descend by the fpqc descent theorems in Mathlib; separatedness uses the Proved https://prove2.me/theorems/bd2d4bb6-3b79-5359-9880-cadfce8f9f9d . This is a finite-extension cover input for the generic-curve-fibration alteration frontier of the Philippon mission; it does not assert semistable reduction or higher-dimensional alteration.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

theorem AlgebraicGeometry.exists_finite_extension_smooth_proper_cover_of_proper_dimension_le_one
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [IsAlgClosed K] {C : Scheme.{u}} (π : C ⟶ Spec (.of k)) [IsProper π]
    (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (Y : Scheme.{u}) (f : Y ⟶ C) (p : Y ⟶ Spec (.of E)),
      IsProper f ∧ Surjective f ∧ Smooth p ∧ IsProper p ∧
      f ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by sorry
