-- Prove2me | Theorems.Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ
-- name    : AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/59034f66-cda1-59be-95f0-81e9a8dde7cd
-- title:
--   Reduced scheme covered by finitely many affine closed subschemes is affine
-- statement:
--   Let $X$ be a scheme (in the bottom universe), let $n$ be a natural number, and let $Z : \mathrm{Fin}\,n \to \mathrm{Scheme}$ be a finite family of schemes equipped with morphisms $i_j : Z_j \to X$ for $j \in \mathrm{Fin}\,n$. Assume that each $i_j$ is a closed immersion, that each $Z_j$ is affine, that $X$ is reduced, and that the images of the underlying continuous maps cover $X$, i.e. $\bigcup_{j} \mathrm{range}\,(i_j)_{\mathrm{base}} = X$ as subsets of the topological space of $X$. The conclusion is that $X$ is affine. The covering hypothesis is set-theoretic surjectivity of the family on points only; no compatibility between the closed subschemes $Z_j$ is assumed, and the case $n = 0$ is included, where the hypothesis forces $X$ to have empty underlying space.
--
--   This is the finite-family form of the statement that a reduced scheme which is the set-theoretic union of finitely many affine closed subschemes is affine. It is used in the construction of affine open neighbourhoods in the study of proper families of relative dimension one, via [`AlgebraicGeometry.exists_isAffineOpen_of_finite_of_isProper_of_forall_smoothOfRelativeDimension_one`](thm.html#AlgebraicGeometry.exists_isAffineOpen_of_finite_of_isProper_of_forall_smoothOfRelativeDimension_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isAffine_of_iUnion_range_eq_univ
    (X : Scheme.{0}) (n : ℕ) (Z : Fin n → Scheme.{0}) (i : ∀ j : Fin n, Z j ⟶ X)
    (hci : ∀ j : Fin n, IsClosedImmersion (i j)) (haff : ∀ j : Fin n, IsAffine (Z j))
    (hred : IsReduced X)
    (hcov : ⋃ j : Fin n, Set.range (i j).base = Set.univ) :
    IsAffine X := by sorry
