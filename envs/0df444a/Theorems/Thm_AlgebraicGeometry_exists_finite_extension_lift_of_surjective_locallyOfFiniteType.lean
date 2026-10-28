-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_finite_extension_lift_of_surjective_locallyOfFiniteType
-- name    : AlgebraicGeometry.exists_finite_extension_lift_of_surjective_locallyOfFiniteType
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T18:52:29.521487+00:00
-- url     : https://prove2.me/theorems/4d0c1a7e-baf7-4340-bd2b-e3834a92f082
-- title:
--   Field-valued points lift through a finite-type cover after a finite extension
-- statement:
--   Let $f:X\to Y$ be a surjective morphism of schemes that is locally of finite type. Let $K$ be any field and let $y:\operatorname{Spec}K\to Y$ be a specified point. There are a finite field extension $L/K$ and a morphism $x:\operatorname{Spec}L\to X$ for which
--   $$f\circ x=y\circ\operatorname{Spec}(K\hookrightarrow L).$$
--   The given $K$-point is therefore recovered exactly after this finite scalar extension. Neither properness nor quasi-compactness or separatedness is required. The finite extension need not be separable.
--
--   This is the finite-field lifting step used after a parameter space has a supplied surjective finite-type cover. In particular, a generic classifying point can lift to a supplied fine parameter cover over a further finite extension. The existence of that cover or of a universal stable-curve family is not asserted here.
-- source:
--   Derived field-valued lifting consequence of the Hilbert Nullstellensatz: Stacks Project Lemma 29.21.3, tag 01TF, https://stacks.math.columbia.edu/tag/01TF . Apply it to a closed point of the nonempty actual pullback X x_Y Spec K, which is locally of finite type over K. In the Philippon boundary-alteration argument this supplies the finite-field lifting part of the parameter-cover step in A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Section 4.17, pp. 71-72, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . It is an elementary auxiliary consequence, not a construction of the stable moduli cover.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

theorem AlgebraicGeometry.exists_finite_extension_lift_of_surjective_locallyOfFiniteType
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Surjective f] [LocallyOfFiniteType f]
    (y : Spec (.of K) ⟶ Y) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (x : Spec (.of L) ⟶ X),
      x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ y := by sorry
