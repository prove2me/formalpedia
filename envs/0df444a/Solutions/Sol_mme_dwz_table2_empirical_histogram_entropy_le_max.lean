-- Prove2me | solution 1 for mme_dwz_table2_empirical_histogram_entropy_le_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:16:03.729438+00:00
-- url     : https://prove2.me/submissions/ecff6888-afac-4631-85c8-2226ad48a20e

import Theorems.Thm_mme_dwz_table2_empirical_histogram_mem_same_marginal
import Theorems.Thm_mme_dwz_same_marginal_entropy_values_bddAbove

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

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
          MME.DWZSquare.sameMarginalEntropyValues ∧
        mme_modern_entropyBits p ≤
          MME.DWZSquare.maxSameMarginalEntropy := by
  classical
  dsimp only
  intro w
  have hmem := mme_dwz_table2_empirical_histogram_mem_same_marginal m hm w
  exact ⟨hmem,
    le_csSup mme_dwz_same_marginal_entropy_values_bddAbove hmem⟩
