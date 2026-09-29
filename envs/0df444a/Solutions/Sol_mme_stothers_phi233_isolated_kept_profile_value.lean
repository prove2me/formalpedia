-- Prove2me | solution 1 for mme_stothers_phi233_isolated_kept_profile_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:12:26.111281+00:00
-- url     : https://prove2.me/submissions/5760a148-a27f-48e3-93b4-19f2b625ddce

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Definitions.Def_mme_stothers_phi233_outer_grading
import Definitions.Def_mme_CW_2376_address_block
import Theorems.Thm_mme_stothers_phi233_isolated_kept_profile_product_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_bigAdd_uniform_strict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

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
        MME.StothersFourth.Phi233.cyclicModeWord e.1 i))
    (tau B : ℝ) (hB : 0 ≤ B)
    (hprofile : ∀ W : ℝ, 0 ≤ W → W < B →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (TensorObj.kronFin 10 (fun r ↦
            (MME.StothersFourth.Phi233.componentObj K q r).kronPow
              (MME.StothersFourth.Phi233.profileMultiplicity
                alpha beta gamma delta r)))) tau W)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < (kept.card : ℝ) * B) :
    HasTauValueAtLeast
      ((cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K q 2 3 3)).kronPow
          (2 * N)) tau V := by
  let P := cyclicSymmetrization
    (TensorObj.kronFin 10 (fun r ↦
      (MME.StothersFourth.Phi233.componentObj K q r).kronPow
        (MME.StothersFourth.Phi233.profileMultiplicity
          alpha beta gamma delta r)))
  have hsum : HasTauValueAtLeast
      (TensorObj.bigAdd (fun _ : Fin kept.card ↦ P)) tau V := by
    apply mme_HasTauValueAtLeast_bigAdd_uniform_strict
      (fun _ : Fin kept.card ↦ P) tau B hB
    · intro _ W hW hWB
      exact hprofile W hW hWB
    · exact hV
    · exact hVlt
  exact mme_HasTauValueAtLeast_mono_restrict
    (mme_stothers_phi233_isolated_kept_profile_product_restrict
      (K := K) q kept hkept hisolated hmode)
    hsum
