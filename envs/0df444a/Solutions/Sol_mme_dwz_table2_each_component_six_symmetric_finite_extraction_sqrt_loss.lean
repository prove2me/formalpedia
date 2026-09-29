-- Prove2me | solution 1 for mme_dwz_table2_each_component_six_symmetric_finite_extraction_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:49:38.590283+00:00
-- url     : https://prove2.me/submissions/9d8af0fd-513c-4f92-825c-c83fc4ade1c7

import Mathlib.Tactic
import Theorems.Thm_mme_dwz_table2_elementary_component_rows_six_symmetric_finite_extraction_sqrt_loss
import Theorems.Thm_mme_dwz_table2_022_202_rows_six_symmetric_finite_extraction_sqrt_loss
import Theorems.Thm_mme_dwz_table2_112_row_six_symmetric_finite_extraction_sqrt_loss
import Theorems.Thm_mme_dwz_table2_121_211_rows_six_symmetric_finite_extraction_sqrt_loss

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
        ∀ s : Fin 15,
          ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd
                (fun j => MMObj K (A j) (B j) (Cdim j)))
              (sixSymmetrization (restrictedComponentPower K s m)) ∧
            (((componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
                Real.exp
                  (-C * Real.sqrt
                    (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨Celem, hCelem, helem⟩ :=
    mme_dwz_table2_elementary_component_rows_six_symmetric_finite_extraction_sqrt_loss
      (K := K) tau htau
  obtain ⟨C022, hC022, h022⟩ :=
    mme_dwz_table2_022_202_rows_six_symmetric_finite_extraction_sqrt_loss
      (K := K) tau htau
  obtain ⟨C112, hC112, h112⟩ :=
    mme_dwz_table2_112_row_six_symmetric_finite_extraction_sqrt_loss
      (K := K) tau htau
  obtain ⟨C121, hC121, h121⟩ :=
    mme_dwz_table2_121_211_rows_six_symmetric_finite_extraction_sqrt_loss
      (K := K) tau htau
  let C : ℝ := Celem + C022 + C112 + C121
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCelemC : Celem ≤ C := by dsimp [C]; nlinarith
  have hC022C : C022 ≤ C := by dsimp [C]; nlinarith
  have hC112C : C112 ≤ C := by dsimp [C]; nlinarith
  have hC121C : C121 ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [helem, h022, h112, h121] with m hmElem hm022 hm112 hm121
  let r : ℝ := Real.sqrt
    (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have lift (s : Fin 15) (Ci : ℝ) (hCiC : Ci ≤ C)
      (hdata :
        ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd
              (fun j => MMObj K (A j) (B j) (Cdim j)))
            (sixSymmetrization (restrictedComponentPower K s m)) ∧
          (((componentBase tau s) ^
              (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
              Real.exp (-Ci * r) ≤
            ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau)) :
        ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd
              (fun j => MMObj K (A j) (B j) (Cdim j)))
            (sixSymmetrization (restrictedComponentPower K s m)) ∧
          (((componentBase tau s) ^
              (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
              Real.exp (-C * r) ≤
            ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
    obtain ⟨q, A, B, Cdim, hrestrict, hweight⟩ := hdata
    refine ⟨q, A, B, Cdim, hrestrict, ?_⟩
    have hexp : Real.exp (-C * r) ≤ Real.exp (-Ci * r) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact (mul_le_mul_of_nonneg_left hexp (by positivity)).trans hweight
  intro s
  fin_cases s
  · exact lift 0 Celem hCelemC
      (by simpa only [r] using hmElem 0 (Or.inl (by norm_num)))
  · exact lift 1 Celem hCelemC
      (by simpa only [r] using hmElem 1 (Or.inl (by norm_num)))
  · exact lift 2 Celem hCelemC
      (by simpa only [r] using hmElem 2 (Or.inl (by norm_num)))
  · exact lift 3 Celem hCelemC
      (by simpa only [r] using hmElem 3 (Or.inl (by norm_num)))
  · exact lift 4 Celem hCelemC
      (by simpa only [r] using hmElem 4 (Or.inl (by norm_num)))
  · exact lift 5 Celem hCelemC
      (by simpa only [r] using hmElem 5 (Or.inl (by norm_num)))
  · exact lift 6 Celem hCelemC
      (by simpa only [r] using hmElem 6 (Or.inl (by norm_num)))
  · exact lift 7 Celem hCelemC
      (by simpa only [r] using hmElem 7 (Or.inl (by norm_num)))
  · exact lift 8 Celem hCelemC
      (by simpa only [r] using hmElem 8 (Or.inl (by norm_num)))
  · exact lift 9 C022 hC022C
      (by simpa only [r] using hm022 9 (Or.inl rfl))
  · exact lift 10 C022 hC022C
      (by simpa only [r] using hm022 10 (Or.inr rfl))
  · exact lift 11 Celem hCelemC
      (by simpa only [r] using hmElem 11 (Or.inr rfl))
  · exact lift 12 C112 hC112C
      (by simpa only [r] using hm112)
  · exact lift 13 C121 hC121C
      (by simpa only [r] using hm121 13 (Or.inl rfl))
  · exact lift 14 C121 hC121C
      (by simpa only [r] using hm121 14 (Or.inr rfl))
