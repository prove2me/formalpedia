-- Prove2me | solution 1 for mme_dwz_table2_reindexed_global_marginal_family_characterization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T01:25:27.436337+00:00
-- url     : https://prove2.me/submissions/674b1785-41a2-43fc-994b-eb398d9eb843

import Theorems.Thm_mme_dwz_table2_exact_profile_coarse_Z_counts

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) (hm : 0 < m)
    (A : Finset
      (Fin ((MME.DWZTable2Counts.scale * m - 1) + 1) → Fin 15)) :
    let L := MME.DWZTable2Counts.scale * m
    let N := L - 1
    let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
      dsimp only [N, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let P : (Fin L → Fin 15) → Prop := fun w ↦
      (∀ x, Fintype.card
          {t : Fin L // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
      (∀ y, Fintype.card
          {t : Fin L // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
      ∀ z, Fintype.card
          {t : Fin L // MME.DWZSquare.shapeZ (w t) = z} =
        MME.DWZTable2Counts.alphaZ z * m
    let A0 : Finset (Fin L → Fin 15) := Finset.univ.filter P
    (∀ a, a ∈ A ↔ ∃ w ∈ A0, (fun t ↦ w (reindex t)) = a) →
    ∀ a, a ∈ A ↔
      (∀ x, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeX (a t) = x} = alphaX x) ∧
      (∀ y, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeY (a t) = y} = alphaY y) ∧
      ∀ z, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeZ (a t) = z} =
        MME.DWZTable2Counts.alphaZ z * m := by
  classical
  dsimp only
  let L := MME.DWZTable2Counts.scale * m
  let N := L - 1
  let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
    dsimp only [N, L]
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
  let alphaX : Fin 5 → ℕ := fun x ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
      MME.DWZTable2Counts.component s.1 * m
  let alphaY : Fin 5 → ℕ := fun y ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
      MME.DWZTable2Counts.component s.1 * m
  let P : (Fin L → Fin 15) → Prop := fun w ↦
    (∀ x, Fintype.card
        {t : Fin L // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
    (∀ y, Fintype.card
        {t : Fin L // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
    ∀ z, Fintype.card
        {t : Fin L // MME.DWZSquare.shapeZ (w t) = z} =
      MME.DWZTable2Counts.alphaZ z * m
  let A0 : Finset (Fin L → Fin 15) := Finset.univ.filter P
  intro hA a
  constructor
  · intro ha
    obtain ⟨w, hwA0, hwa⟩ := (hA a).mp ha
    have hwP : P w := (Finset.mem_filter.mp hwA0).2
    subst a
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (Fintype.card_congr
        (reindex.subtypeEquiv (fun _ ↦ Iff.rfl))).trans (hwP.1 x)
    · intro y
      exact (Fintype.card_congr
        (reindex.subtypeEquiv (fun _ ↦ Iff.rfl))).trans (hwP.2.1 y)
    · intro z
      exact (Fintype.card_congr
        (reindex.subtypeEquiv (fun _ ↦ Iff.rfl))).trans (hwP.2.2 z)
  · rintro ⟨hx, hy, hz⟩
    let w : Fin L → Fin 15 := fun t ↦ a (reindex.symm t)
    apply (hA a).mpr
    refine ⟨w, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · intro x
        exact (Fintype.card_congr
          (reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl))).trans (hx x)
      · intro y
        exact (Fintype.card_congr
          (reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl))).trans (hy y)
      · intro z
        exact (Fintype.card_congr
          (reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl))).trans (hz z)
    · funext t
      dsimp only [w]
      congr 1
