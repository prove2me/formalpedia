-- Prove2me | solution 1 for mme_dwz_q6_canonical_112_source_router_Z_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T07:39:33.397226+00:00
-- url     : https://prove2.me/submissions/084d4660-495a-4042-ac95-d7a8111d8874

import Theorems.Thm_mme_dwz_q6_canonical_112_basis_labelled_source_router
import Theorems.Thm_mme_dwz_q6_112_Z_decoder_pair_and_leftGrade
import Theorems.Thm_mme_dwz_q6_canonicalComponent112_Z_basis_eq_blockProj

open MME PiTensorProduct Module

universe u

set_option autoImplicit false
set_option maxHeartbeats 400000

open MME.DWZComponentRestriction

/-- The public canonical-112 router, specialized to its exact action on the
literal row-112 Z basis. -/
theorem solution
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (canonicalComponentBlock K 12).V s →ₗ[K]
          (coupledObj K 6).V s,
      PiTensorProduct.map maps (canonicalComponentBlock K 12).t =
          (coupledObj K 6).t ∧
      ∀ p : LiftedCoarsePair.{u} 6 2,
        maps 2 (canonicalComponentZBasis K 12 p) =
          dwzQ6CoupledBasis K 2 (dwzQ6Canonical112ZCoord p) := by
  obtain ⟨maps, ht, hb⟩ :=
    mme_dwz_q6_canonical_112_basis_labelled_source_router K
  refine ⟨maps, ht, ?_⟩
  intro p
  rw [mme_dwz_q6_canonicalComponent112_Z_basis_eq_blockProj]
  rw [← (mme_dwz_q6_112_Z_decoder_pair_and_leftGrade p).1]
  have h := hb 2 (dwzQ6Canonical112ZCoord p)
  change maps 2
      ((cwSquareCanonicalGrading K 6).blockProj 2 2
        (cwSquareCanonicalBasis K 6 2
          (dwzCanonical112Pair 6 2 (dwzQ6Canonical112ZCoord p)))) =
      dwzCanonical112Vec K 6 2 (dwzQ6Canonical112ZCoord p) at h
  exact h.trans (dwzQ6CoupledBasis_apply K 2 _).symm
