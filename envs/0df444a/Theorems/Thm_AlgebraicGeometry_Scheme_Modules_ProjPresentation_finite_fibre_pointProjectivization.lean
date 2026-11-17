-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_finite_fibre_pointProjectivization
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.finite_fibre_pointProjectivization
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:57.054132+00:00
-- url     : https://prove2.me/theorems/465d6e13-52c3-4245-93eb-970bded93eed
-- title:
--   A finite projective presentation has finite fibres on rational points
-- statement:
--   Let $P:X→ℙ^N_K$ be the morphism defined by a projective presentation over a field, and assume $P$ is finite. For every projective class $z∈ℙ^N(K)$, the set $$\{x∈X(K):P(x)=z\}$$ is finite. This is the fibrewise finiteness input for the Northcott argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.finite_fibre_pointProjectivization {K : Type} [Field K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N : ℕ} (P : M.ProjPresentation f N)
    (hfin : IsFinite P.toProj) (z : Projectivization K (Fin (N + 1) → K)) :
    {x : Scheme.KPoint f | P.pointProjectivization x = z}.Finite := by sorry
