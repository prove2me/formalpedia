-- Prove2me | solution 1 for mme_stothers_phi233_isolated_kept_blocks_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:03:55.534168+00:00
-- url     : https://prove2.me/submissions/3a4e21da-1a44-4827-b7dd-6643b9ba7bea

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Definitions.Def_mme_stothers_phi233_cyclic_grading_address
import Definitions.Def_mme_stothers_phi233_outer_grading
import Theorems.Thm_mme_type2_ambient_isolated_induced_and_blocks_restrict
import Theorems.Thm_mme_stothers_phi233_cyclic_target_ambient_closure
import Theorems.Thm_mme_cyclic_triple_grading_nonzero_factors
import Theorems.Thm_mme_stothers_phi233_outer_grading_support

open MME

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace MME.StothersFourth.Phi233

private theorem cyclic_block_supports_mixed_addresses
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (es : Fin 3 → CyclicAmbientEdge N alpha beta gamma delta)
    (hblocks : ∀ j : Fin (2 * N),
      (mmeCyclicTripleGrading (outerGrading K q)).blockTensor
        (fun i ↦ cyclicGradingAddress (es i) i j) ≠ 0) :
    CyclicCoordinatewiseSupported (es 0) (es 1) (es 2) := by
  let rhoX : Fin 3 → Fin (2 * N) → Fin 5 := fun s ↦ (es s).1.1 s
  let rhoY : Fin 3 → Fin (2 * N) → Fin 5 := fun s ↦
    (es (cyclicPerm s)).2.1.1 s
  let rhoZ : Fin 3 → Fin (2 * N) → Fin 5 := fun s ↦
    (es ((cyclicPerm.trans cyclicPerm) s)).2.2.1 s
  have hfactors : ∀ j : Fin (2 * N),
      (outerGrading K q).blockTensor (fun s ↦ rhoX s j) ≠ 0 ∧
      (outerGrading K q).blockTensor (fun s ↦ rhoY s j) ≠ 0 ∧
      (outerGrading K q).blockTensor (fun s ↦ rhoZ s j) ≠ 0 := by
    intro j
    apply mme_cyclic_triple_grading_nonzero_factors
      (outerGrading K q)
        (fun s ↦ rhoX s j) (fun s ↦ rhoY s j) (fun s ↦ rhoZ s j)
    have hgrade :
        (fun i ↦ cyclicGradingAddress (es i) i j) =
          mmeCyclicTripleGrade
            (fun s ↦ rhoX s j) (fun s ↦ rhoY s j)
              (fun s ↦ rhoZ s j) := by
      funext i
      fin_cases i <;> rfl
    rw [← hgrade]
    exact hblocks j
  constructor
  · intro j
    obtain ⟨r, hr⟩ := mme_stothers_phi233_outer_grading_support
      q (fun s ↦ rhoX s j) (hfactors j).1
    refine ⟨r, ?_⟩
    calc
      addressType (mixedAddress (es 0).1 (es 1).1 (es 2).1) j =
          (fun s ↦ rhoX s j) := by
            funext i
            fin_cases i <;> rfl
      _ = pattern r := hr
  · constructor
    · intro j
      obtain ⟨r, hr⟩ := mme_stothers_phi233_outer_grading_support
        q (fun s ↦ rhoY s j) (hfactors j).2.1
      refine ⟨r, ?_⟩
      calc
        addressType
            (mixedAddress (es 1).2.1 (es 2).2.1 (es 0).2.1) j =
            (fun s ↦ rhoY s j) := by
              funext i
              fin_cases i <;> rfl
        _ = pattern r := hr
    · intro j
      obtain ⟨r, hr⟩ := mme_stothers_phi233_outer_grading_support
        q (fun s ↦ rhoZ s j) (hfactors j).2.2
      refine ⟨r, ?_⟩
      calc
        addressType
            (mixedAddress (es 2).2.2 (es 0).2.2 (es 1).2.2) j =
            (fun s ↦ rhoZ s j) := by
              funext i
              fin_cases i <;> rfl
        _ = pattern r := hr

end MME.StothersFourth.Phi233

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
    (∀ x y z : kept,
      MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported
          x.1 y.1 z.1 →
        x = y ∧ y = z) ∧
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin kept.card ↦
        gradedAddressBlock
          (mmeCyclicTripleGrading
            (MME.StothersFourth.Phi233.outerGrading K q))
          (MME.StothersFourth.Phi233.cyclicGradingAddress
            (kept.equivFin.symm j).1)))
      ((cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K q 2 3 3)).kronPow
          (2 * N)) := by
  classical
  have hclosure :=
    mme_stothers_phi233_cyclic_target_ambient_closure
      N alpha beta gamma delta
  apply mme_type2_ambient_isolated_induced_and_blocks_restrict
    (mmeCyclicTripleGrading
      (MME.StothersFourth.Phi233.outerGrading K q))
    MME.StothersFourth.Phi233.cyclicGradingAddress
    (fun i e ↦ MME.StothersFourth.Phi233.cyclicModeWord e i)
    MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported
    (MME.StothersFourth.Phi233.ambientFinset
      N alpha beta gamma delta)
    (MME.StothersFourth.Phi233.targetFinset
      N alpha beta gamma delta)
    kept hkept hclosure.2 hisolated hmode
  intro es hblocks
  exact MME.StothersFourth.Phi233.cyclic_block_supports_mixed_addresses
    q (fun i ↦ (es i).1) hblocks
