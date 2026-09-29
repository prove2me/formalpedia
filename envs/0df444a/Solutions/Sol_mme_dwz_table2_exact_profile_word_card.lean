-- Prove2me | solution 1 for mme_dwz_table2_exact_profile_word_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T20:53:17.168396+00:00
-- url     : https://prove2.me/submissions/68d92ed3-d624-4a94-a6e6-cf1d91a0c590

import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Set.Card

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

theorem solution (m : ℕ) :
    (Finset.univ.filter fun w :
        Fin (MME.DWZTable2Counts.scale * m) → Fin 15 ↦
          ∀ s, Fintype.card {t // w t = s} =
            MME.DWZTable2Counts.component s * m).card =
      Nat.multinomial Finset.univ
        (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) := by
  classical
  let L : ℕ := MME.DWZTable2Counts.scale * m
  let counts : Fin 15 → ℕ := fun s ↦
    MME.DWZTable2Counts.component s * m
  let P : (Fin L → Fin 15) → Prop := fun w ↦
    ∀ s, Fintype.card {t // w t = s} = counts s
  have hsum : ∑ s, counts s = Fintype.card (Fin L) := by
    dsimp only [counts, L]
    rcases mme_dwz_table2_integer_counts_exact with
      ⟨_, _, _, hcomponent, _⟩
    rw [← Finset.sum_mul, hcomponent]
    simp only [Fintype.card_fin]
  have h := mme_fintype_prescribed_fiber_function_card counts hsum
  have hNat : Nat.card
        {w : Fin L → Fin 15 //
          ∀ s, Fintype.card {t // w t = s} = counts s} =
      (Fintype.card (Fin L)).factorial /
        ∏ s : Fin 15, (counts s).factorial := by
    simpa only [Fintype.card_eq_nat_card] using h
  rw [show MME.DWZTable2Counts.scale * m = L from rfl]
  calc
    (Finset.univ.filter fun w : Fin L → Fin 15 ↦
        ∀ s, Fintype.card {t // w t = s} =
          MME.DWZTable2Counts.component s * m).card =
        ({w : Fin L → Fin 15 | P w} : Set (Fin L → Fin 15)).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext w
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and, Set.mem_ofPred_eq, P, counts]
    _ = Nat.card ({w : Fin L → Fin 15 | P w} : Set (Fin L → Fin 15)) :=
      (Nat.card_coe_set_eq
        ({w : Fin L → Fin 15 | P w} : Set (Fin L → Fin 15))).symm
    _ = (Fintype.card (Fin L)).factorial /
          ∏ s : Fin 15, (counts s).factorial := by
      exact hNat
    _ = Nat.multinomial Finset.univ counts := by
      simp only [Nat.multinomial, hsum]
    _ = Nat.multinomial Finset.univ
          (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) := rfl
