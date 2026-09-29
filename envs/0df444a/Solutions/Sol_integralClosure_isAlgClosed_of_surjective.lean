-- Prove2me | solution 1 for integralClosure.isAlgClosed_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/ddcd0bb9-f851-5ad0-9a20-dadd407f9957

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_integralClosure_isAlgClosed_of_surjective

set_option autoImplicit false

open Polynomial

namespace IntegralClosureResidue

theorem isAlgClosed_of_surjective {R L F : Type*} [CommRing R] [Field L] [IsAlgClosed L]
    [Algebra R L] [Field F] (φ : integralClosure R L →+* F) (hφ : Function.Surjective φ) :
    IsAlgClosed F := by
  refine IsAlgClosed.of_exists_root F fun f hf hirr => ?_

  obtain ⟨g, hgf, hdeg, hgmon⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic (Polynomial.mem_lifts_of_surjective hφ f) hf

  have hdegL : (g.map (algebraMap (integralClosure R L) L)).degree ≠ 0 := by
    rw [hgmon.degree_map, hdeg]
    exact fun h => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr h |>.elim
      (fun u hu => ⟨u, hu⟩))
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdegL

  have hαint : IsIntegral (integralClosure R L) α := ⟨g, hgmon, by
    rw [Polynomial.eval₂_eq_eval_map]; exact hα⟩
  have hαR : IsIntegral R α := isIntegral_trans (R := R) α hαint
  let a : integralClosure R L := ⟨α, hαR⟩
  have hga : g.eval a = 0 := by
    have h1 : algebraMap (integralClosure R L) L (g.eval a) = 0 := by
      have h2 : (g.map (algebraMap (integralClosure R L) L)).eval
          (algebraMap (integralClosure R L) L a) = 0 := hα
      rwa [Polynomial.eval_map, Polynomial.eval₂_at_apply] at h2
    exact (FaithfulSMul.algebraMap_injective (integralClosure R L) L)
      (by rw [h1, map_zero])
  refine ⟨φ a, ?_⟩
  rw [← hgf, Polynomial.eval_map, Polynomial.eval₂_at_apply, hga, map_zero]

end IntegralClosureResidue

theorem solution
    {R L F : Type*} [CommRing R] [Field L] [IsAlgClosed L] [Algebra R L] [Field F]
    (φ : integralClosure R L →+* F) (hφ : Function.Surjective φ) :
    IsAlgClosed F :=
  IntegralClosureResidue.isAlgClosed_of_surjective φ hφ

end S_integralClosure_isAlgClosed_of_surjective
end P2MW
export P2MW.S_integralClosure_isAlgClosed_of_surjective (solution)
