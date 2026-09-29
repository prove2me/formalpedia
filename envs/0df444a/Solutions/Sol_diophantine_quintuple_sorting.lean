-- Prove2me | solution 1 for diophantine_quintuple_sorting
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T02:58:33.172267+00:00
-- url     : https://prove2.me/submissions/dc5efe76-839f-4e6e-9f3e-eb9207907e53

import Definitions.Def_diophantine_descent
import Mathlib.Data.Finset.Sort
set_option autoImplicit false
open DiophantineDescent

theorem solution (f : Fin 5 → Nat) (hq : Quintuple f) :
    ∃ g : Fin 5 → Nat, Quintuple g ∧ Ordered g ∧ (∀ i, ∃ j, g i = f j) := by
  obtain ⟨hpos, hinj, hsq⟩ := hq
  have hinj' : Function.Injective f := by
    intro a b hab
    by_contra hne
    exact hinj a b hne hab
  have hcard : (Finset.image f Finset.univ).card = 5 := by
    rw [Finset.card_image_of_injective _ hinj']
    simp
  set g : Fin 5 → Nat := fun i => (Finset.image f Finset.univ).orderEmbOfFin hcard i with hg_def
  refine ⟨g, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i
      have hm := Finset.orderEmbOfFin_mem _ hcard i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
      simp only [hg_def]
      rw [← hj]; exact hpos j
    · intro i j hij
      exact (Finset.orderEmbOfFin _ hcard).injective.ne hij
    · intro i j hij
      have hmi := Finset.orderEmbOfFin_mem _ hcard i
      have hmj := Finset.orderEmbOfFin_mem _ hcard j
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hmi
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hmj
      simp only [hg_def]
      have hab : a ≠ b := by
        intro heq
        apply hij
        apply (Finset.orderEmbOfFin _ hcard).injective
        rw [← ha, ← hb, heq]
      obtain ⟨r, hr⟩ := hsq a b hab
      exact ⟨r, by rw [← ha, ← hb]; exact hr⟩
  · have hmono := (Finset.orderEmbOfFin _ hcard).strictMono
    simp only [hg_def]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply hmono <;> decide
  · intro i
    have hm := Finset.orderEmbOfFin_mem _ hcard i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    simp only [hg_def]
    exact ⟨j, hj.symm⟩
