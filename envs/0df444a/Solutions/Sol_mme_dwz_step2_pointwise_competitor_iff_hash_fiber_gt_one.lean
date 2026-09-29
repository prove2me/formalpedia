-- Prove2me | solution 1 for mme_dwz_step2_pointwise_competitor_iff_hash_fiber_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T21:16:33.088469+00:00
-- url     : https://prove2.me/submissions/8f67e956-fda5-4ae1-9f9d-a99b6fc793d8

import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Outer Weight : Type*}
    [Fintype Outer] [DecidableEq Outer]
    (compatible : Outer → Prop) [DecidablePred compatible]
    (hashRetained : Outer → Weight → Prop)
    [DecidableRel hashRetained]
    (retained : Outer) (w : Weight)
    (hRetainedCompatible : compatible retained)
    (hRetainedHash : hashRetained retained w) :
    1 < (Finset.univ.filter
        (fun A : Outer ↦ compatible A ∧ hashRetained A w)).card ↔
      ∃ A : Outer,
        A ≠ retained ∧ compatible A ∧ hashRetained A w := by
  classical
  let fiber : Finset Outer :=
    Finset.univ.filter
      (fun A : Outer ↦ compatible A ∧ hashRetained A w)
  have hRetainedMem : retained ∈ fiber := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ retained, hRetainedCompatible, hRetainedHash⟩
  constructor
  · intro hFiber
    change 1 < fiber.card at hFiber
    have hErasePos : 0 < (fiber.erase retained).card := by
      have hEraseCard := Finset.card_erase_of_mem hRetainedMem
      omega
    obtain ⟨A, hAErase⟩ := Finset.card_pos.mp hErasePos
    have hAData := Finset.mem_erase.mp hAErase
    have hAMem := Finset.mem_filter.mp hAData.2
    exact ⟨A, hAData.1, hAMem.2.1, hAMem.2.2⟩
  · rintro ⟨A, hANe, hACompatible, hAHash⟩
    change 1 < fiber.card
    have hAMem : A ∈ fiber := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ A, hACompatible, hAHash⟩
    have hErasePos : 0 < (fiber.erase retained).card := by
      apply Finset.card_pos.mpr
      exact ⟨A, Finset.mem_erase.mpr ⟨hANe, hAMem⟩⟩
    have hEraseCard := Finset.card_erase_of_mem hRetainedMem
    omega
