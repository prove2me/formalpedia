-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_surjective_cover_of_isProper
-- name    : AlgebraicGeometry.exists_smooth_projective_surjective_cover_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-13T16:19:12.505507+00:00
-- url     : https://prove2.me/theorems/a6b6c200-a786-44eb-9ce6-1a8e43d60a39
-- title:
--   A smooth projective scheme surjecting onto a proper scheme
-- statement:
--   Let $X$ be a proper scheme over an algebraically closed field $K$. There exist a smooth projective $K$-scheme $Y$ and a proper surjective $K$-morphism $f:Y\to X$.
--
--   Projectivity is given explicitly: for some integer $n\geq0$ and closed immersion $i$, the structure morphisms $p_n:\mathbf P^n_K\to\operatorname{Spec}K$ and $\pi:X\to\operatorname{Spec}K$ satisfy
--
--   $$i:Y\hookrightarrow\mathbf P^n_K,\qquad p_n\circ i=\pi\circ f.$$
--
--   The scheme $Y$ need not be integral or connected. No reducedness or irreducibility is assumed for $X$, and the empty scheme is allowed. This is the algebraically closed field case of the cited alteration lemma, with a projective embedding displayed. It supplies a smooth projective cover for descent arguments on general proper schemes.
-- source:
--   Cheng, Ji, Larson and Olander, Theorem of the Base (1 July 2021), Lemma 6.1, p. 16: https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf. Specialize the perfect field to an algebraically closed field; exhibit the projective embedding. The proof takes the finite disjoint union of smooth projective alterations of the reduced irreducible components, using de Jong, Smoothness, semi-stability and alterations, Theorem 4.1. Properness of the map is also Stacks Project, Lemma 29.42.7 (https://stacks.math.columbia.edu/tag/01W0).

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_smooth_projective_surjective_cover_of_isProper
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
        ∃ (n : ℕ)
          (i : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)),
          IsClosedImmersion i ∧ i ≫ ProjSpace.π K n = f ≫ π := by
  sorry
