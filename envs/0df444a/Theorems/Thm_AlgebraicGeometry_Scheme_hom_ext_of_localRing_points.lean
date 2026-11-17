-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_hom_ext_of_localRing_points
-- name    : AlgebraicGeometry.Scheme.hom_ext_of_localRing_points
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:23.110746+00:00
-- url     : https://prove2.me/theorems/2359978d-03a7-4d1d-b5f9-c6f74d56f9d2
-- title:
--   Scheme morphisms are determined by all local-ring-valued points
-- statement:
--   Let $u,v:X→Y$ be morphisms of schemes. If for every local ring $K$ and every point $p:Spec(K)→X$ one has $u∘p=v∘p$, then $$u=v.$$ This extensionality principle turns pointwise verification of the carry law into equality of scheme morphisms.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.hom_ext_of_localRing_points {X Y : Scheme.{0}} (u v : X ⟶ Y)
    (h : ∀ (K : Type) [CommRing K] [IsLocalRing K]
      (p : Spec (CommRingCat.of K) ⟶ X), p ≫ u = p ≫ v) : u = v := by sorry
