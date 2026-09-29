-- Prove2me | solution 1 for mme_dwz_step1_filtered_source_distinct_xy_exists_zero_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:46:34.486441+00:00
-- url     : https://prove2.me/submissions/0c673f74-d2d8-4010-a5dc-0b09ab7e7c77

import Definitions.Def_mme_dwz_step1_broken_owner_maps

open MME
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {k N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (hXYOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        (cwSquareCanonicalGrading K 6).blockTensor
          (fun i ↦ coarseAddress (outer (js i)) i r) ≠ 0) →
      js 0 = js 1)
    (js : Fin 3 → Fin k) (h01 : js 0 ≠ js 1) :
    ∃ r : Fin N,
      (cwSquareCanonicalGrading K 6).blockTensor
        (fun i ↦ coarseAddress (outer (js i)) i r) = 0 := by
  have hnotSupported : ¬ ∀ r : Fin N,
      (cwSquareCanonicalGrading K 6).blockTensor
        (fun i ↦ coarseAddress (outer (js i)) i r) ≠ 0 := by
    intro hsupported
    exact h01 (hXYOwner js hsupported)
  obtain ⟨r, hr⟩ := Classical.not_forall.mp hnotSupported
  exact ⟨r, by simpa only [not_ne_iff] using hr⟩
