-- Prove2me | solution 1 for mme_dwz_square_source_aligned_broken_family_ungrouped_aggregate_hash_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:02:27.239599+00:00
-- url     : https://prove2.me/submissions/a6ada7f8-ad82-4b30-b2d0-ef5d0469eedc

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Definitions.Def_mme_dwz_hole_cover_data
import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Theorems.Thm_mme_dwz_table2_global_common_q_source_aggregate_raw_mass
import Theorems.Thm_mme_dwz_table2_global_exact_profile_hash_mass_and_prime_upper

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] :
    ∀ᶠ m : ℕ in atTop,
      let L : ℕ := MME.DWZTable2Counts.scale * m
      let x : ℝ := (((L + 1 : ℕ) : ℝ))
      let jointPoly : ℝ := (6 * x) ^ 15
      let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
      let zPoly : ℝ := (6 * x) ^ 5
      let compatibilityPoly : ℝ := (6 * x) ^ 9
      let Dhash : ℝ :=
        32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly)
      ∃ (n p : ℕ)
          (outer : Fin n → Fin L → Fin 15)
          (copies : ∀ r : Fin n, BrokenBlockCopy
            (MME.DWZTable2StandardForm.UsefulBlock m (outer r))),
        let A : ℝ :=
          Real.rpow 2 (retainedLogRate * (L : ℝ)) *
            (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
                Real.exp
                  (-4 * Real.sqrt
                    (Real.log (((p / 2 : ℕ) : ℝ))))) /
              Dhash)
        0 < m ∧
        2 ≤ p ∧
        (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) ∧
        (∀ r s,
          Fintype.card {t : Fin L // outer r t = s} =
            MME.DWZTable2Counts.component s * m) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun r ↦
            MME.DWZSourceAligned.brokenAddressObj K m
              (outer r) (copies r)))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L) ∧
        A ≤ ∑ r, nonholeFraction (copies r) := by
  filter_upwards
    [mme_dwz_table2_global_common_q_source_aggregate_raw_mass (K := K)]
      with m hm
  dsimp only at hm ⊢
  rcases hm with
    ⟨n, p, N, fixedTargetCard, d, Q, R, S, reindex, q, edge,
      hmpos, hp2, hfactor, hdpos, hd, hR, hp, hdPow, hQPow, hpNat,
      hbehrend, hprofile, hrestrict, hraw⟩
  let outer : Fin n → Fin (MME.DWZTable2Counts.scale * m) → Fin 15 :=
    fun r ↦ MME.DWZGlobalCorrelated.sourceWord reindex edge r
  let copies : ∀ r : Fin n, BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m (outer r)) :=
    fun r ↦ MME.DWZGlobalCorrelated.commonStateBrokenCopy
      m reindex q edge r
  let mass : ℝ := ∑ r, nonholeFraction (copies r)
  have hppos : 0 < p := lt_of_lt_of_le (by norm_num) hp2
  have hnorm :=
    mme_dwz_table2_global_exact_profile_hash_mass_and_prime_upper
      m hmpos
      (Nat.multinomial Finset.univ
        (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m))
      fixedTargetCard d Q p R mass S rfl hfactor hdpos hppos
      hd hR hp hdPow hQPow hpNat hbehrend
      (by simpa only [mass, copies, outer] using hraw)
  dsimp only at hnorm
  rcases hnorm with ⟨hpExp, hmass⟩
  refine ⟨n, p, outer, copies, ?_⟩
  refine ⟨hmpos, hp2, hpExp, ?_, ?_, ?_⟩
  · simpa only [outer] using hprofile
  · simpa only [outer, copies] using hrestrict
  · convert hmass using 1
    ring
