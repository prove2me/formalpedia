-- Prove2me | solution 1 for mme_dwz_table2_022_202_rows_six_symmetric_finite_extraction_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T06:55:23.992857+00:00
-- url     : https://prove2.me/submissions/ac73226f-fa87-4ef8-8c2d-729455481a5a

import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_mme_dwz_q6_022_202_table2_scaled_rows_one_MM_restrict
import Theorems.Thm_mme_dwz_q6_022_table2_scaled_dimension_six_finite_rate
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_sixSymmetrization_MMObj_isomorphic
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_rank_bridge

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction
open MME.DWZTable2Component022

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZCentral022PublicReduction

theorem bigAdd_one_isomorphic
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun _ : Fin 1 ↦ T)) T := by
  apply (TensorQ.toQ_eq_iff).1
  rw [TensorQ.toQ_bigAdd]
  simp

theorem oneMM_six_restrict
    {K : Type u} [Field K] {Y : TensorObj K 3}
    (a b c : ℕ) (h : TensorObj.Restrict (MMObj K a b c) Y) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin 1 ↦
        MMObj K ((a * b * c) ^ 2) ((a * b * c) ^ 2)
          ((a * b * c) ^ 2)))
      (sixSymmetrization Y) := by
  let Q : TensorObj K 3 :=
    MMObj K ((a * b * c) ^ 2) ((a * b * c) ^ 2)
      ((a * b * c) ^ 2)
  have hsingle := bigAdd_one_isomorphic Q
  have hsixMM := mme_sixSymmetrization_MMObj_isomorphic
    (K := K) a b c
  have hsixRestrict := mme_sixSymmetrization_restrict h
  exact TensorObj.Restrict.trans hsingle.1
    (TensorObj.Restrict.trans hsixMM.2 hsixRestrict)

theorem six_rpow_eq_square_volume (d : ℕ) (tau : ℝ) :
    (((d : ℝ) ^ tau) ^ (6 : ℕ)) =
      (((d ^ 2) * (d ^ 2) * (d ^ 2) : ℕ) : ℝ) ^ tau := by
  rw [Real.rpow_pow_comm (Nat.cast_nonneg d) tau 6]
  congr 1
  push_cast
  ring

end MME.DWZCentral022PublicReduction

open MME.DWZCentral022PublicReduction

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 9 ∨ s = 10) →
          ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd (fun j => MMObj K (A j) (B j) (Cdim j)))
              (sixSymmetrization (restrictedComponentPower K s m)) ∧
            (((componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨C, hC, hrate⟩ :=
    mme_dwz_q6_022_table2_scaled_dimension_six_finite_rate tau htau
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrate] with m hm
  intro s hs
  let D := Nat.card (Restricted022Word 6
    (table2Power022 (10366945 * m))
    (table2OuterCount022 (10366945 * m))
    (table2MiddleCount022 (10366945 * m)))
  have hrows :=
    mme_dwz_q6_022_202_table2_scaled_rows_one_MM_restrict K m
  change TensorObj.Restrict (MMObj K 1 1 D)
      (restrictedComponentPower K (9 : Fin 15) m) ∧
    TensorObj.Restrict (MMObj K D 1 1)
      (restrictedComponentPower K (10 : Fin 15) m) at hrows
  change (((componentBase tau (9 : Fin 15)) ^
      (MME.DWZTable2Counts.component 9 * m)) ^ (6 : ℕ)) *
        Real.exp (-C * Real.sqrt
          (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
    (((D : ℕ) : ℝ) ^ tau) ^ (6 : ℕ) at hm
  rcases hs with hs | hs
  · subst s
    have hrestrict := oneMM_six_restrict 1 1 D hrows.1
    refine ⟨1, (fun _ ↦ D ^ 2), (fun _ ↦ D ^ 2),
      (fun _ ↦ D ^ 2), ?_, ?_⟩
    · simpa only [one_mul] using hrestrict
    · rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      rw [← six_rpow_eq_square_volume D tau]
      exact hm
  · subst s
    have hrestrict := oneMM_six_restrict D 1 1 hrows.2
    refine ⟨1, (fun _ ↦ D ^ 2), (fun _ ↦ D ^ 2),
      (fun _ ↦ D ^ 2), ?_, ?_⟩
    · simpa only [mul_one] using hrestrict
    · rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      rw [← six_rpow_eq_square_volume D tau]
      have h9 : componentBase tau (9 : Fin 15) =
          componentBase tau (10 : Fin 15) := by
        norm_num [componentBase, Fin.ext_iff]
      have hc9 : MME.DWZTable2Counts.component (9 : Fin 15) =
          MME.DWZTable2Counts.component (10 : Fin 15) := by
        rfl
      rw [h9, hc9] at hm
      exact hm
