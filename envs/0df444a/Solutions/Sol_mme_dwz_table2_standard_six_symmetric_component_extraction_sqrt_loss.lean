-- Prove2me | solution 1 for mme_dwz_table2_standard_six_symmetric_component_extraction_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:42:50.190522+00:00
-- url     : https://prove2.me/submissions/0f4e7149-3e49-4689-bd9a-2bbbd6587647

import Mathlib.Tactic
import Definitions.Def_mme_dwz_table2_standard_obj
import Theorems.Thm_mme_dwz_table2_each_component_six_symmetric_finite_extraction_sqrt_loss
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product
import Theorems.Thm_mme_sixSymmetrization_kronFin_isomorphic

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd
              (fun j => MMObj K (A j) (B j) (Cdim j)))
            (sixSymmetrization (dwzTable2StandardObj K m)) ∧
          ((∏ s : Fin 15,
              (componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨Clocal, hClocal, hlocal⟩ :=
    mme_dwz_table2_each_component_six_symmetric_finite_extraction_sqrt_loss
      (K := K) tau htau
  let C : ℝ := 15 * Clocal
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hlocal] with m hm
  let sroot : ℝ := Real.sqrt
    (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))
  let lower : Fin 15 → ℝ := fun i =>
    (((componentBase tau i) ^
      (MME.DWZTable2Counts.component i * m)) ^ (6 : ℕ)) *
        Real.exp (-Clocal * sroot)
  have hlower : ∀ i, 0 ≤ lower i := by
    intro i
    dsimp [lower]
    positivity
  have hextract : ∀ i : Fin 15,
      ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd
            (fun j => MMObj K (A j) (B j) (Cdim j)))
          (sixSymmetrization (restrictedComponentPower K i m)) ∧
        lower i ≤
          ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
    intro i
    simpa only [lower, sroot] using hm i
  obtain ⟨q, A, B, Cdim, hrestrict, hweight⟩ :=
    mme_finite_MM_extractions_kronFin_tau_product
      (K := K)
      (fun i : Fin 15 => sixSymmetrization
        (restrictedComponentPower K i m))
      tau lower hlower hextract
  refine ⟨q, A, B, Cdim, ?_, ?_⟩
  · have hiso := mme_sixSymmetrization_kronFin_isomorphic
      (K := K) (fun i : Fin 15 => restrictedComponentPower K i m)
    have hsource : TensorObj.Restrict
        (TensorObj.kronFin 15
          (fun i => sixSymmetrization (restrictedComponentPower K i m)))
        (sixSymmetrization (dwzTable2StandardObj K m)) := by
      simpa only [dwzTable2StandardObj] using hiso.1
    exact TensorObj.Restrict.trans hrestrict hsource
  · have hlowerProduct :
        (∏ i : Fin 15, lower i) =
          ((∏ i : Fin 15,
              (componentBase tau i) ^
                (MME.DWZTable2Counts.component i * m)) ^ (6 : ℕ)) *
            Real.exp (-C * sroot) := by
      calc
        (∏ i : Fin 15, lower i) =
            (∏ i : Fin 15,
              ((componentBase tau i) ^
                (MME.DWZTable2Counts.component i * m)) ^ (6 : ℕ)) *
              (∏ _i : Fin 15, Real.exp (-Clocal * sroot)) := by
                dsimp only [lower]
                exact Finset.prod_mul_distrib
        _ = ((∏ i : Fin 15,
              (componentBase tau i) ^
                (MME.DWZTable2Counts.component i * m)) ^ (6 : ℕ)) *
              (Real.exp (-Clocal * sroot)) ^ (15 : ℕ) := by
                rw [Finset.prod_pow, Finset.prod_const,
                  Finset.card_fin]
        _ = ((∏ i : Fin 15,
              (componentBase tau i) ^
                (MME.DWZTable2Counts.component i * m)) ^ (6 : ℕ)) *
              Real.exp (-C * sroot) := by
                rw [← Real.exp_nat_mul]
                congr 2
                dsimp [C]
                ring
    change
      ((∏ i : Fin 15,
          (componentBase tau i) ^
            (MME.DWZTable2Counts.component i * m)) ^ (6 : ℕ)) *
          Real.exp (-C * sroot) ≤
        ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau)
    rw [← hlowerProduct]
    exact hweight
