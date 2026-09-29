-- Prove2me | solution 1 for mme_dwz_table2_scaled_shape_marginals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:04:10.758793+00:00
-- url     : https://prove2.me/submissions/70665660-ad5f-4a54-8447-6b99b6ae2d20

import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

namespace MME.DWZScaledMarginals

private theorem component_marginal
    (coord : Fin 15 → Fin 5) (i : Fin 5) :
    ((∑ s : {s : Fin 15 // coord s = i},
        MME.DWZTable2Counts.component s.1 : ℕ) : ℝ) /
        (MME.DWZTable2Counts.scale : ℝ) =
      mme_modern_marginal coord MME.DWZSquare.alpha i := by
  classical
  rcases mme_dwz_table2_integer_counts_exact with ⟨hcomponent, _⟩
  have hscale : (MME.DWZTable2Counts.scale : ℝ) ≠ 0 := by
    norm_num [MME.DWZTable2Counts.scale]
  unfold mme_modern_marginal
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  apply (div_eq_iff hscale).2
  simpa only [mul_comm] using (hcomponent s.1).symm

theorem proof (m : ℕ) (hm : 0 < m) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    (∀ x, (alphaX x : ℝ) / (sourceLength : ℝ) =
      mme_modern_marginal MME.DWZSquare.shapeX MME.DWZSquare.alpha x) ∧
    (∀ y, (alphaY y : ℝ) / (sourceLength : ℝ) =
      mme_modern_marginal MME.DWZSquare.shapeY MME.DWZSquare.alpha y) ∧
    ∀ z, (MME.DWZTable2Counts.alphaZ z * m : ℕ) /
        (sourceLength : ℝ) =
      mme_modern_marginal MME.DWZSquare.shapeZ MME.DWZSquare.alpha z := by
  classical
  dsimp only
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · intro x
    rw [← Finset.sum_mul, Nat.cast_mul, Nat.cast_sum]
    push_cast
    rw [mul_div_mul_right _ _ hmR]
    simpa only [Nat.cast_sum, mme_modern_marginal] using
      (component_marginal MME.DWZSquare.shapeX x)
  constructor
  · intro y
    rw [← Finset.sum_mul, Nat.cast_mul, Nat.cast_sum]
    push_cast
    rw [mul_div_mul_right _ _ hmR]
    simpa only [Nat.cast_sum, mme_modern_marginal] using
      (component_marginal MME.DWZSquare.shapeY y)
  · intro z
    push_cast
    rw [mul_div_mul_right _ _ hmR]
    rcases mme_dwz_table2_integer_counts_exact with
      ⟨_, _, _, _, _, _, _, _, hAlphaZ, _⟩
    apply (div_eq_iff (show
      (MME.DWZTable2Counts.scale : ℝ) ≠ 0 by
        norm_num [MME.DWZTable2Counts.scale])).2
    simpa only [mul_comm] using (hAlphaZ z).symm

end MME.DWZScaledMarginals

theorem solution (m : ℕ) (hm : 0 < m) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    (∀ x, (alphaX x : ℝ) / (sourceLength : ℝ) =
      mme_modern_marginal MME.DWZSquare.shapeX MME.DWZSquare.alpha x) ∧
    (∀ y, (alphaY y : ℝ) / (sourceLength : ℝ) =
      mme_modern_marginal MME.DWZSquare.shapeY MME.DWZSquare.alpha y) ∧
    ∀ z, (MME.DWZTable2Counts.alphaZ z * m : ℕ) /
        (sourceLength : ℝ) =
      mme_modern_marginal MME.DWZSquare.shapeZ MME.DWZSquare.alpha z :=
  MME.DWZScaledMarginals.proof m hm
