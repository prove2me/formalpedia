-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_integral_projective
-- name    : AlgebraicGeometry.exists_smooth_projective_cover_of_integral_projective
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-23T15:01:50.162973+00:00
-- url     : https://prove2.me/theorems/458ae238-c2b5-482b-9660-62cc2a0119f6
-- title:
--   Smooth integral projective cover of an integral projective variety
-- statement:
--   Let $K$ be an algebraically closed field and let $X$ be an integral proper $K$-scheme equipped with a closed immersion into a projective space over $K$. There exist an integral smooth projective $K$-scheme $Y$ and a proper surjective $K$-morphism
--   $$f:Y\longrightarrow X.$$
--   Projectivity of $Y$ is exhibited by a closed immersion $j:Y\hookrightarrow\mathbb P^m_K$ whose composite with the structural map to $\operatorname{Spec}K$ is the structural map $f$ followed by that of $X$.
--
--   This is the proper projective case of the regular-alteration theorem over a perfect field, retaining the smooth integral source and forgetting the additional generic-finiteness and normal-crossing assertions. No restriction on the characteristic or the dimension is imposed. The zero-dimensional case is included.
--
--   **Formalization Note.** Both projective embeddings are actual morphisms to the existing Proj model, with explicit compatibility with the base field.
-- source:
--   Derived specialization of A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathematiques de l IHES 83 (1996), Theorem 4.1 and Remark 4.2, p.66, and the proper/projective reduction in Section 4.7, p.67; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . An algebraically closed field is perfect; regular finite-type schemes over it are smooth. For proper X, the alteration source is proper, so its open immersion into the regular projective compactification is an isomorphism. The generic-finiteness and boundary-divisor conclusions of Theorem 4.1 are omitted. This is a derived consequence, not a literal transcription of the full theorem. Also used in Cheng, Ji, Larson and Olander, Theorem of the Base (2021), Lemma 6.1, p.16, https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf .

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_smooth_projective_cover_of_integral_projective
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π := by sorry
