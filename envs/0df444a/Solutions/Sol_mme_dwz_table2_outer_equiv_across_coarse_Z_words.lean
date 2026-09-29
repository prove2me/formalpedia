-- Prove2me | solution 1 for mme_dwz_table2_outer_equiv_across_coarse_Z_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:03:33.914004+00:00
-- url     : https://prove2.me/submissions/7dd8afee-815b-4c3b-b7be-4ae8c0e89a45

import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_square_data

set_option autoImplicit false
set_option warningAsError true

private noncomputable def outerReindex
    (m : ℕ) {L : ℕ} (K₁ K₂ : Fin L → Fin 5)
    (e : Fin L ≃ Fin L) (he : ∀ t, K₂ (e t) = K₁ t)
    (w : {w : Fin L → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K₁ t) ∧
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m}) :
    {w : Fin L → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K₂ t) ∧
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m} := by
  classical
  refine ⟨fun t ↦ w.1 (e.symm t), ?_, ?_⟩
  · intro t
    calc
      MME.DWZSquare.shapeZ (w.1 (e.symm t)) = K₁ (e.symm t) :=
        w.2.1 (e.symm t)
      _ = K₂ t := by simpa using (he (e.symm t)).symm
  · intro s
    let fiberEquiv :
        {t : Fin L // w.1 (e.symm t) = s} ≃
          {t : Fin L // w.1 t = s} :=
      Equiv.subtypeEquiv e.symm (fun _ ↦ Iff.rfl)
    exact (Fintype.card_congr fiberEquiv).trans (w.2.2 s)

theorem solution
    (m : ℕ) {L : ℕ} (K₁ K₂ : Fin L → Fin 5)
    (hK₁ : ∀ z, Fintype.card {t : Fin L // K₁ t = z} =
      MME.DWZTable2Counts.alphaZ z * m)
    (hK₂ : ∀ z, Fintype.card {t : Fin L // K₂ t = z} =
      MME.DWZTable2Counts.alphaZ z * m) :
    let Outer₁ :=
      {w : Fin L → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K₁ t) ∧
        ∀ s, Fintype.card {t : Fin L // w t = s} =
          MME.DWZTable2Counts.component s * m}
    let Outer₂ :=
      {w : Fin L → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K₂ t) ∧
        ∀ s, Fintype.card {t : Fin L // w t = s} =
          MME.DWZTable2Counts.component s * m}
    ∃ e : Fin L ≃ Fin L, (∀ t, K₂ (e t) = K₁ t) ∧
      ∃ E : Outer₁ ≃ Outer₂,
        ∀ w t, (E w).1 (e t) = w.1 t := by
  classical
  dsimp only
  let fiberEquiv : ∀ z : Fin 5,
      {t : Fin L // K₁ t = z} ≃ {t : Fin L // K₂ t = z} := fun z ↦
    Fintype.equivOfCardEq ((hK₁ z).trans (hK₂ z).symm)
  let e : Fin L ≃ Fin L := Equiv.ofFiberEquiv fiberEquiv
  have he : ∀ t, K₂ (e t) = K₁ t := Equiv.ofFiberEquiv_map fiberEquiv
  have heSymm : ∀ t, K₁ (e.symm t) = K₂ t := by
    intro t
    simpa using (he (e.symm t)).symm
  let E :
      {w : Fin L → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K₁ t) ∧
        ∀ s, Fintype.card {t : Fin L // w t = s} =
          MME.DWZTable2Counts.component s * m} ≃
      {w : Fin L → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K₂ t) ∧
        ∀ s, Fintype.card {t : Fin L // w t = s} =
          MME.DWZTable2Counts.component s * m} :=
    { toFun := outerReindex m K₁ K₂ e he
      invFun := outerReindex m K₂ K₁ e.symm heSymm
      left_inv := by
        intro w
        apply Subtype.ext
        funext t
        simp [outerReindex]
      right_inv := by
        intro w
        apply Subtype.ext
        funext t
        simp [outerReindex] }
  refine ⟨e, he, E, ?_⟩
  intro w t
  simp [E, outerReindex]
