-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_affine_etale_cover_factor_of_forall_mem_range_of_etale
-- name    : AlgebraicGeometry.exists_affine_etale_cover_factor_of_forall_mem_range_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/c04f0281-3bbc-5a07-8f52-16f744399a2d
-- title:
--   Étale-local sections through a jointly surjective étale family
-- statement:
--   Let $T$ and $N$ be schemes with $T$ affine, let $y : T \to N$ be a morphism, let $\iota$ be an index type, let $X : \iota \to \mathrm{Sch}$ be a family of schemes and let $h_i : X_i \to N$ be morphisms, each étale. Assume the family is jointly surjective on points: every point $z$ of $N$ lies in the range of some $h_i$ on underlying topological spaces. Then there exist a natural number $n$, indices $i : \mathrm{Fin}\,n \to \iota$, schemes $T'_j$ for $j \in \mathrm{Fin}\,n$, each affine, morphisms $c_j : T'_j \to T$, each étale, and morphisms $w_j : T'_j \to X_{i_j}$, such that the $c_j$ are jointly surjective on points (every point $t$ of $T$ lies in the range of some $c_j$) and such that for every $j$ the square commutes: $w_j$ followed by $h_{i_j}$ equals $c_j$ followed by $y$. Thus $y$ lifts through the given family after passage to a finite étale covering family of the affine scheme $T$ by affine schemes.
--
--   This is the standard statement that a morphism from an affine scheme into $N$ admits sections through a jointly surjective étale family after an étale covering of the source, with the covering taken finite and by affine schemes (using quasi-compactness of the affine $T$). It serves as a generic geometric input for the fpqc-local lifting step in the Čerednik–Drinfeld part of the development, being cited by [`CerednikDrinfeld.QM.IsFineModuli.exists_flat_family_lift_of_cerednikDrinfeld_uniformization_fine`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_flat_family_lift_of_cerednikDrinfeld_uniformization_fine) and [`CerednikDrinfeld.QM.exists_flat_family_lift_of_formallyEtale_of_locallyOfFiniteType`](thm.html#CerednikDrinfeld.QM.exists_flat_family_lift_of_formallyEtale_of_locallyOfFiniteType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_affine_etale_cover_factor_of_forall_mem_range_of_etale.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_affine_etale_cover_factor_of_forall_mem_range_of_etale
    {T N : Scheme.{u}} [IsAffine T] (y : T ⟶ N)
    {ι : Type v} (X : ι → Scheme.{u}) (h : ∀ i, X i ⟶ N) [∀ i, Etale (h i)]
    (hsurj : ∀ z : N, ∃ i, z ∈ Set.range (h i)) :
    ∃ (n : ℕ) (i : Fin n → ι) (T' : Fin n → Scheme.{u}) (_ : ∀ j, IsAffine (T' j))
      (c : ∀ j, T' j ⟶ T) (_ : ∀ j, Etale (c j)) (w : ∀ j, T' j ⟶ X (i j)),
      (∀ t : T, ∃ j, t ∈ Set.range (c j)) ∧ ∀ j, w j ≫ h (i j) = c j ≫ y := by sorry
