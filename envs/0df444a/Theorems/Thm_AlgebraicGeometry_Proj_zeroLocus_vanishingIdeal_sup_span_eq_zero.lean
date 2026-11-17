-- Prove2me | Theorems.Thm_AlgebraicGeometry_Proj_zeroLocus_vanishingIdeal_sup_span_eq_zero
-- name    : AlgebraicGeometry.Proj.zeroLocus_vanishingIdeal_sup_span_eq_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:23.747692+00:00
-- url     : https://prove2.me/theorems/3e8270f6-f634-4acc-b914-6dce00b9cde8
-- title:
--   A projective open cover forces the corresponding affine cone intersection to be the origin
-- statement:
--   Let $V$ be a closed subset of a projective spectrum, and let selected coordinate opens $D_+(X_{inc(i)})$ cover $V$. If $z$ over an algebraic closure annihilates the vanishing ideal of $V$ and all selected coordinates, then $$z=0.$$ This is the projective-to-affine zero-locus statement used to obtain homogeneous Bézout certificates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial
open AlgebraicGeometry
open AlgebraicGeometry.Proj

theorem AlgebraicGeometry.Proj.zeroLocus_vanishingIdeal_sup_span_eq_zero
    {K S T : Type} [Field K] [Fintype S] [Fintype T]
    (V : Set (ProjectiveSpectrum (homogeneousSubmodule S K)))
    (hV : IsClosed V) (inc : T → S)
    (hcover : ∀ x ∈ V, ∃ i : T,
      (X (inc i) : MvPolynomial S K) ∉ x.asHomogeneousIdeal) :
    ∀ z : S → AlgebraicClosure K,
      z ∈ MvPolynomial.zeroLocus (AlgebraicClosure K)
        ((ProjectiveSpectrum.vanishingIdeal V).toIdeal ⊔
          Ideal.span (Set.range (fun i : T => (X (inc i) : MvPolynomial S K)))) →
      z = 0 := by sorry
