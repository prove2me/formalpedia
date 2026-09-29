-- Prove2me | solution 1 for mme_dwz_retained_enumeration_common_z_y_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T11:00:02.870979+00:00
-- url     : https://prove2.me/submissions/2c7d0542-21e4-44c1-8f45-667b32bc5dff

import Definitions.Def_mme_dwz_square_data

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {L N k : ℕ} {Outer : Type*}
    (reindex : Fin (N + 1) ≃ Fin L)
    (K : Fin L → Fin 5)
    (I : Finset (Fin (N + 1) → Fin 15))
    (word : Outer → Fin L → Fin 15)
    (hWordInjective : Function.Injective word)
    (outer : Fin k → Outer)
    (hOuterInjective : Function.Injective outer)
    (hFixedZ : ∀ j t,
      MME.DWZSquare.shapeZ (word (outer j) t) = K t)
    (hBack : ∀ j, ∃ a ∈ I,
      word (outer j) = fun t ↦ a (reindex.symm t))
    (hYIsolatedSource : ∀ a ∈ I, ∀ b ∈ I,
      (fun t ↦ MME.DWZSquare.shapeY (a t)) =
          (fun t ↦ MME.DWZSquare.shapeY (b t)) →
        a = b) :
    (∀ j j' t,
      MME.DWZSquare.shapeZ (word (outer j) t) =
        MME.DWZSquare.shapeZ (word (outer j') t)) ∧
    ∀ j j',
      (fun t ↦ MME.DWZSquare.shapeY (word (outer j) t)) =
          (fun t ↦ MME.DWZSquare.shapeY (word (outer j') t)) →
        j = j' := by
  constructor
  · intro j j' t
    rw [hFixedZ j t, hFixedZ j' t]
  · intro j j' hY
    obtain ⟨a, haI, hja⟩ := hBack j
    obtain ⟨b, hbI, hjb⟩ := hBack j'
    have hSourceY :
        (fun t ↦ MME.DWZSquare.shapeY (a t)) =
          (fun t ↦ MME.DWZSquare.shapeY (b t)) := by
      funext t
      have ht := congrFun hY (reindex t)
      simpa only [hja, hjb, Equiv.symm_apply_apply] using ht
    have hab : a = b := hYIsolatedSource a haI b hbI hSourceY
    apply hOuterInjective
    apply hWordInjective
    rw [hja, hjb, hab]
