-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_charZero_point_specializes_of_natCast_mem_maximalIdeal_of_not_isNilpotent
-- name    : AlgebraicGeometry.Scheme.exists_charZero_point_specializes_of_natCast_mem_maximalIdeal_of_not_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/a4c74e1e-d00c-520e-b81c-046c12da0ffd
-- title:
--   Characteristic-zero generisation through a non-nilpotent integer
-- statement:
--   Let $X$ be a scheme (in universe $u$), let $x$ be a point of $X$, and let $n$ be a natural number. Assume that the image of $n$ under the canonical ring homomorphism $\mathbb{N} \to \mathcal{O}_{X,x}$, the stalk of the structure sheaf of $X$ at $x$, lies in the maximal ideal of that local ring, and that this image is not nilpotent in $\mathcal{O}_{X,x}$. Then there exist a type $K$ in universe $u$, a field structure on $K$, a proof that $K$ has characteristic zero, and a morphism of schemes $\xi : \operatorname{Spec} K \to X$ such that for every point $z$ of $\operatorname{Spec} K$ the image point $\xi(z)$ specialises to $x$, i.e. $x$ lies in the closure of $\{\xi(z)\}$. (Since $\operatorname{Spec} K$ has a single point for $K$ a field, the last clause says that the unique image point of $\xi$ is a generisation of $x$.)",
--
--   The statement produces, from a point $x$ whose local ring contains $n$ in its maximal ideal without $n$ being nilpotent, a characteristic-zero point of $X$ generising $x$; for a scheme over $\mathbb{Z}$ this makes the generic fibre non-empty. It is used in the construction of fake elliptic curves attached to quaternionic Shimura curves, to produce a point over a characteristic-zero field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_charZero_point_specializes_of_natCast_mem_maximalIdeal_of_not_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_charZero_point_specializes_of_natCast_mem_maximalIdeal_of_not_isNilpotent
    {X : Scheme.{u}} (x : X) (n : ℕ)
    (hn : ((n : ℕ) : X.presheaf.stalk x) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hnil : ¬ IsNilpotent ((n : ℕ) : X.presheaf.stalk x)) :
    ∃ (K : Type u) (_ : Field K) (_ : CharZero K) (ξ : Spec (CommRingCat.of K) ⟶ X),
      ∀ z : Spec (CommRingCat.of K), ξ.base z ⤳ x := by sorry
