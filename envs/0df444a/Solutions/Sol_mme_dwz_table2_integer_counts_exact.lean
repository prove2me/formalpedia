-- Prove2me | solution 1 for mme_dwz_table2_integer_counts_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T12:07:12.93942+00:00
-- url     : https://prove2.me/submissions/76faa85a-a8ae-465d-a0af-f39d04199b93

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts

open BigOperators Finset
open MME.DWZSquare
open MME.DWZTable2Counts

set_option autoImplicit false

private theorem component_exact (s : Fin 15) :
    (scale : ℝ) * alpha s = component s := by
  fin_cases s <;> norm_num [scale, alpha, component] <;> rfl

private theorem split_exact (s : Fin 15) (r : Fin 3) :
    (scale : ℝ) * alpha s * zSplit s r =
      MME.DWZTable2Counts.split s r := by
  fin_cases s <;> fin_cases r <;>
    simp [scale, alpha, zSplit, MME.DWZTable2Counts.split,
      shapeZ, splitA, splitB] <;> norm_num

private theorem split_sum (s : Fin 15) :
    ∑ r, MME.DWZTable2Counts.split s r = component s := by
  fin_cases s <;>
    norm_num [MME.DWZTable2Counts.split, component, Fin.sum_univ_succ]

private theorem component_sum :
    ∑ s, MME.DWZTable2Counts.component s = scale := by
  norm_num [component, scale, Fin.sum_univ_succ]

private theorem gamma_sum :
    ∑ p, MME.DWZTable2Counts.gamma p = scale := by
  rw [Fintype.sum_prod_type]
  norm_num [MME.DWZTable2Counts.gamma, scale, Fin.sum_univ_succ]

private theorem alphaZ_sum : ∑ k, alphaZ k = scale := by
  norm_num [alphaZ, scale, Fin.sum_univ_succ]

private theorem plusSplit_sum (k : Fin 5) :
    ∑ r, MME.DWZTable2Counts.plusSplit k r =
      MME.DWZTable2Counts.plusMass k := by
  fin_cases k <;>
    norm_num [MME.DWZTable2Counts.plusSplit,
      MME.DWZTable2Counts.plusMass, Fin.sum_univ_succ]

private theorem gamma_exact (p : Fin 3 × Fin 3) :
    (scale : ℝ) * MME.DWZSquare.gamma p =
      MME.DWZTable2Counts.gamma p := by
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [scale, MME.DWZSquare.gamma,
      MME.DWZTable2Counts.gamma, shapeZ, alpha, zSplit,
      splitA, splitB, Fin.sum_univ_succ] <;> norm_num

private theorem alphaZ_exact (k : Fin 5) :
    (scale : ℝ) * mme_modern_marginal shapeZ alpha k =
      MME.DWZTable2Counts.alphaZ k := by
  classical
  unfold mme_modern_marginal
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun s : Fin 15 ↦ shapeZ s = k)) (by simp)]
  fin_cases k <;> rw [Finset.sum_filter] <;>
    simp [scale, shapeZ, alpha, MME.DWZTable2Counts.alphaZ,
      Fin.sum_univ_succ] <;> norm_num

private theorem plusMass_exact (k : Fin 5) :
    (scale : ℝ) * MME.DWZSquare.plusMass k =
      MME.DWZTable2Counts.plusMass k := by
  fin_cases k <;>
    simp [scale, MME.DWZSquare.plusMass,
      MME.DWZTable2Counts.plusMass, shapeX, shapeY, shapeZ, alpha,
      Fin.sum_univ_succ] <;> norm_num

private theorem plusSplit_exact (k : Fin 5) (r : Fin 3) :
    (scale : ℝ) * MME.DWZSquare.plusMass k *
        MME.DWZSquare.plusSplit k r =
      MME.DWZTable2Counts.plusSplit k r := by
  fin_cases k <;> fin_cases r <;>
    simp [scale, MME.DWZSquare.plusMass, MME.DWZSquare.plusSplit,
      MME.DWZTable2Counts.plusSplit, shapeX, shapeY, shapeZ,
      alpha, zSplit, splitA, splitB, Fin.sum_univ_succ]
  all_goals norm_num

theorem solution :
    (∀ s : Fin 15,
      (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.alpha s =
        MME.DWZTable2Counts.component s) ∧
    (∀ s : Fin 15, ∀ r : Fin 3,
      (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.alpha s *
          MME.DWZSquare.zSplit s r =
        MME.DWZTable2Counts.split s r) ∧
    (∀ s : Fin 15,
      ∑ r, MME.DWZTable2Counts.split s r =
        MME.DWZTable2Counts.component s) ∧
    (∑ s, MME.DWZTable2Counts.component s =
      MME.DWZTable2Counts.scale) ∧
    (∑ p, MME.DWZTable2Counts.gamma p =
      MME.DWZTable2Counts.scale) ∧
    (∑ k, MME.DWZTable2Counts.alphaZ k =
      MME.DWZTable2Counts.scale) ∧
    (∀ k : Fin 5,
      ∑ r, MME.DWZTable2Counts.plusSplit k r =
        MME.DWZTable2Counts.plusMass k) ∧
    (∀ p : Fin 3 × Fin 3,
      (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.gamma p =
        MME.DWZTable2Counts.gamma p) ∧
    (∀ k : Fin 5,
      (MME.DWZTable2Counts.scale : ℝ) *
          mme_modern_marginal MME.DWZSquare.shapeZ MME.DWZSquare.alpha k =
        MME.DWZTable2Counts.alphaZ k) ∧
    (∀ k : Fin 5,
      (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.plusMass k =
        MME.DWZTable2Counts.plusMass k) ∧
    ∀ k : Fin 5, ∀ r : Fin 3,
      (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.plusMass k *
          MME.DWZSquare.plusSplit k r =
        MME.DWZTable2Counts.plusSplit k r := by
  exact ⟨component_exact, split_exact, split_sum, component_sum,
    gamma_sum, alphaZ_sum, plusSplit_sum, gamma_exact, alphaZ_exact,
    plusMass_exact, plusSplit_exact⟩
