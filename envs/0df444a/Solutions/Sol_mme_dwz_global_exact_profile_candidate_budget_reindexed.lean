-- Prove2me | solution 1 for mme_dwz_global_exact_profile_candidate_budget_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T01:57:37.529182+00:00
-- url     : https://prove2.me/submissions/ea00b9ca-ca70-4b53-b510-4fef49b7c803

import Definitions.Def_mme_dwz_retained_fine_compatibility
import Definitions.Def_mme_dwz_table2_useful_block

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) (hm : 0 < m) {p : ℕ} :
    let L := MME.DWZTable2Counts.scale * m
    let N := L - 1
    let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
      dsimp only [N, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let ExactProfile : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
      ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
        MME.DWZTable2Counts.component s * m
    let ExactProfileNative : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m
    let T : Finset (Fin (N + 1) → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfile
    let Tnative : Finset (Fin L → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfileNative
    let NativeOwner := {w : Fin L → Fin 15 // ExactProfileNative w}
    let native : (Fin (N + 1) → Fin 15) → Fin L → Fin 15 :=
      fun a t ↦ a (reindex.symm t)
    let grade : ∀ a,
        MME.DWZTable2StandardForm.UsefulBlock m (native a) →
          Fin L → Fin (3 * 3) := fun _ z t ↦
      MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
    (∀ retained : NativeOwner,
      ∀ z : MME.DWZTable2StandardForm.UsefulBlock m retained.1,
        8 * ((by
          classical
          exact Tnative.filter (fun w : Fin L → Fin 15 ↦
            (∀ t, MME.DWZSquare.shapeZ (w t) =
              MME.DWZSquare.shapeZ (retained.1 t)) ∧
            MME.DWZStep2Source.retainedFineCompatible m
              (fun w : Fin L → Fin 15 ↦ w)
              (fun t ↦ MME.DWZStep1Support.fineSplitGrade
                (z.1 t).1 (z.1 t).2) w)) :
          Finset (Fin L → Fin 15)).card ≤ p) →
    ∀ a, a ∈ T →
      ∀ z : MME.DWZTable2StandardForm.UsefulBlock m (native a),
        8 * ((by
          classical
          exact Tnative.filter (fun w : Fin L → Fin 15 ↦
            (∀ t, MME.DWZSquare.shapeZ (w t) =
              MME.DWZSquare.shapeZ (native a t)) ∧
            MME.DWZStep2Source.retainedFineCompatible m
              (fun w : Fin L → Fin 15 ↦ w) (grade a z) w)) :
          Finset (Fin L → Fin 15)).card ≤ p := by
  classical
  dsimp only
  let L := MME.DWZTable2Counts.scale * m
  let N := L - 1
  let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
    dsimp only [N, L]
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
  let ExactProfile : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
    ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
      MME.DWZTable2Counts.component s * m
  let ExactProfileNative : (Fin L → Fin 15) → Prop := fun w ↦
    ∀ s, Fintype.card {t : Fin L // w t = s} =
      MME.DWZTable2Counts.component s * m
  let T : Finset (Fin (N + 1) → Fin 15) :=
    Finset.univ.filter ExactProfile
  let Tnative : Finset (Fin L → Fin 15) :=
    Finset.univ.filter ExactProfileNative
  let NativeOwner := {w : Fin L → Fin 15 // ExactProfileNative w}
  let native : (Fin (N + 1) → Fin 15) → Fin L → Fin 15 :=
    fun a t ↦ a (reindex.symm t)
  let grade : ∀ a,
      MME.DWZTable2StandardForm.UsefulBlock m (native a) →
        Fin L → Fin (3 * 3) := fun _ z t ↦
    MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
  intro hbudget a ha z
  have hnative : ExactProfileNative (native a) := by
    intro s
    let E : {t : Fin L // native a t = s} ≃
        {t : Fin (N + 1) // a t = s} :=
      reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl)
    calc
      Fintype.card {t : Fin L // native a t = s} =
          Fintype.card {t : Fin (N + 1) // a t = s} :=
        Fintype.card_congr E
      _ = MME.DWZTable2Counts.component s * m :=
        (Finset.mem_filter.mp ha).2 s
  let retained : NativeOwner := ⟨native a, hnative⟩
  simpa only [retained, grade] using hbudget retained z
