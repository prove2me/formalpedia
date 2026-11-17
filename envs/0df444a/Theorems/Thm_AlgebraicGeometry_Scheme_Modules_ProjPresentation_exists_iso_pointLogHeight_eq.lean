-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_pointLogHeight_eq
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_iso_pointLogHeight_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:21.524537+00:00
-- url     : https://prove2.me/theorems/40698bd1-3a83-4a0d-8769-74fcd316cd7f
-- title:
--   Transporting a presentation across a module isomorphism preserves its map and height exactly
-- statement:
--   Let $P$ be a projective presentation of a module $M$ on a scheme over a number field, and let $M≅T$. There exists a presentation $Q$ of $T$ with $$Q_{proj}=P_{proj},\qquad h_Q(x)=h_P(x)\text{ for every rational point }x.$$ This allows line-bundle isomorphisms to be used without changing the chosen height.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_iso_pointLogHeight_eq
    {K : Type} [Field K] [NumberField K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M T : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) (e : M ≅ T) :
    ∃ Q : T.ProjPresentation f N, Q.toProj = P.toProj ∧
      ∀ x : Scheme.KPoint f, Q.pointLogHeight x = P.pointLogHeight x := by sorry
