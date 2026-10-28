-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_finite_extension_smooth_projective_cover_of_scalarExtension_of_proper_dimension_le_one
-- name    : AlgebraicGeometry.exists_finite_extension_smooth_projective_cover_of_scalarExtension_of_proper_dimension_le_one
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-25T19:03:32.611211+00:00
-- url     : https://prove2.me/theorems/a0fdd6ed-d4f7-42ef-8b17-f8add5de7610
-- title:
--   Smooth projective covers of actual scalar-extended curves over finite intermediate fields
-- statement:
--   Let $k$ be a field, let $K/k$ be an algebraic extension with $K$ algebraically closed, and let $C$ be a proper $k$-scheme of dimension at most one. There exist a finite intermediate field $k\subset E\subset K$ and a smooth projective $E$-scheme $Y$ of dimension at most one with a proper surjective $E$-morphism
--   $$\alpha:Y\longrightarrow C_E=C\times_{\operatorname{Spec}k}\operatorname{Spec}E.$$
--   The target is the actual scalar extension along the given intermediate-field inclusion. The structure map of $Y$ is exactly the composite of $\alpha$ with the second projection. Its composite $f:Y\to C$ with the first projection is also proper and surjective and has the exact scalar compatibility. Projectivity is exhibited by a closed immersion $Y\hookrightarrow\mathbb P^n_E$ with the given structure map.
--
--   The curve $C$ may be reducible, nonreduced, disconnected or empty. The extension $K/k$ may be infinite, and $Y$ need not be integral. Surjectivity is retained on the whole actual base-changed curve, so this statement can be applied directly when spreading generic covering maps after a finite extension of the generic field. A finite-field cover of $C$ alone does not imply that its induced map to every chosen scalar extension is surjective. This theorem constructs a cover with the stated stronger property. Semistable reduction and global alteration remain separate.
-- source:
--   Strengthens the finite projective cover construction https://prove2.me/theorems/549dc14e-93eb-467f-8710-7df999574585 by retaining a proper surjection to the actual scalar extension. Reuses its accepted proof construction and four Proved inputs: geometric curve covers https://prove2.me/theorems/98944e77-2d0a-41a3-bad1-20bd6211e2e8 , relative field descent https://prove2.me/theorems/8113d2fc-8253-4a8a-a56e-405a6f283432 , projective-space base change https://prove2.me/theorems/b0c3d8f6-bffa-515d-a45a-3c3271585c3d , and descent of closed immersions https://prove2.me/theorems/15a640ab-f9cc-514b-bd68-f574dde1accc . The actual scalar-extension factor is surjective because its base change to the prescribed algebraically closed field is the original surjective geometric cover. This supplies the genuine scalar-extended generic-cover input for the Philippon alteration branch; semistable and global alteration remain separate.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_finite_extension_smooth_projective_cover_of_scalarExtension_of_proper_dimension_le_one
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [IsAlgClosed K] {C : Scheme.{u}} (π : C ⟶ Spec (.of k)) [IsProper π]
    (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E)
      (Y : Scheme.{u}) (f : Y ⟶ C) (p : Y ⟶ Spec (.of E)),
      IsProper f ∧ Surjective f ∧ Smooth p ∧ IsProper p ∧
      topologicalKrullDim Y ≤ 1 ∧
      f ≫ π = p ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
      ∃ (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π E n = p ∧
          ∃ a : Y ⟶ pullback π (Spec.map (CommRingCat.ofHom (algebraMap k E))),
            a ≫ pullback.fst π _ = f ∧ a ≫ pullback.snd π _ = p ∧
            IsProper a ∧ Surjective a := by sorry
