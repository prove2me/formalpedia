-- Prove2me | solution 1 for mme_stothers_phi233_isolated_kept_profile_product_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:08:20.614492+00:00
-- url     : https://prove2.me/submissions/2c2ef91c-68ff-482b-92b3-a4bfb081ce72

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Definitions.Def_mme_stothers_phi233_outer_grading
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_stothers_phi233_isolated_kept_blocks_restrict
import Theorems.Thm_mme_stothers_phi233_exact_cyclic_component_product_restrict_address_block

open MME

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (kept : Finset
      (MME.StothersFourth.Phi233.CyclicAmbientEdge
        N alpha beta gamma delta))
    (hkept : kept ⊆
      MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta)
    (hisolated :
      ∀ e ∈ MME.StothersFourth.Phi233.ambientFinset
          N alpha beta gamma delta,
        (∀ i : Fin 3, ∃ f ∈ kept,
          MME.StothersFourth.Phi233.cyclicModeWord e i =
            MME.StothersFourth.Phi233.cyclicModeWord f i) →
        e ∈ kept)
    (hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦
        MME.StothersFourth.Phi233.cyclicModeWord e.1 i)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin kept.card ↦
        cyclicSymmetrization
          (TensorObj.kronFin 10 (fun r ↦
            (MME.StothersFourth.Phi233.componentObj K q r).kronPow
              (MME.StothersFourth.Phi233.profileMultiplicity
                alpha beta gamma delta r)))))
      ((cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K q 2 3 3)).kronPow
          (2 * N)) := by
  classical
  have hblocks :=
    (mme_stothers_phi233_isolated_kept_blocks_restrict
      (K := K) q kept hkept hisolated hmode).2
  apply TensorObj.Restrict.trans ?_ hblocks
  apply mme_bigAdd_mono_restrict
  intro j
  have hj : (kept.equivFin.symm j).1 ∈
      MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta :=
    hkept (kept.equivFin.symm j).2
  rw [MME.StothersFourth.Phi233.targetFinset] at hj
  obtain ⟨e, -, he⟩ := Finset.mem_map.mp hj
  rw [← he]
  exact
    mme_stothers_phi233_exact_cyclic_component_product_restrict_address_block
      (K := K) q e
