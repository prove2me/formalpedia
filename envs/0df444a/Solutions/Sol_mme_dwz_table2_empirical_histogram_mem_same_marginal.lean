-- Prove2me | solution 1 for mme_dwz_table2_empirical_histogram_mem_same_marginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:11:42.74307+00:00
-- url     : https://prove2.me/submissions/1dda172f-387a-470e-ace5-f4c3f65a7b66

import Theorems.Thm_mme_empirical_word_probability_and_marginal
import Theorems.Thm_mme_dwz_table2_scaled_shape_marginals

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

theorem solution (m : ℕ) (hm : 0 < m) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let MarginalTriple :=
      {w : Fin sourceLength → Fin 15 //
        (∀ x, Fintype.card
            {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
        (∀ y, Fintype.card
            {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
        ∀ z, Fintype.card
            {t // MME.DWZSquare.shapeZ (w t) = z} =
              MME.DWZTable2Counts.alphaZ z * m}
    ∀ w : MarginalTriple,
      let p : Fin 15 → ℝ := fun s ↦
        (Fintype.card {t : Fin sourceLength // w.1 t = s} : ℝ) /
          (sourceLength : ℝ)
      mme_modern_entropyBits p ∈
        MME.DWZSquare.sameMarginalEntropyValues := by
  classical
  dsimp only
  intro w
  let sourceLength := MME.DWZTable2Counts.scale * m
  let p : Fin 15 → ℝ := fun s ↦
    (Fintype.card {t : Fin sourceLength // w.1 t = s} : ℝ) /
      (sourceLength : ℝ)
  have hsourcePos : 0 < sourceLength := by
    dsimp only [sourceLength]
    exact Nat.mul_pos (by norm_num [MME.DWZTable2Counts.scale]) hm
  have hX := mme_empirical_word_probability_and_marginal sourceLength hsourcePos
    w.1 MME.DWZSquare.shapeX
  have hY := mme_empirical_word_probability_and_marginal sourceLength hsourcePos
    w.1 MME.DWZSquare.shapeY
  have hZ := mme_empirical_word_probability_and_marginal sourceLength hsourcePos
    w.1 MME.DWZSquare.shapeZ
  have hScale := mme_dwz_table2_scaled_shape_marginals m hm
  refine ⟨p, hX.1, hX.2.1, ?_, ?_, ?_, rfl⟩
  · intro x
    rw [hX.2.2 x, w.2.1 x]
    exact hScale.1 x
  · intro y
    rw [hY.2.2 y, w.2.2.1 y]
    exact hScale.2.1 y
  · intro z
    rw [hZ.2.2 z, w.2.2.2 z]
    exact hScale.2.2 z
