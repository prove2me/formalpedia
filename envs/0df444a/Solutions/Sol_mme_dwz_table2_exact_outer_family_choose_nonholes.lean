-- Prove2me | solution 1 for mme_dwz_table2_exact_outer_family_choose_nonholes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T11:49:22.13368+00:00
-- url     : https://prove2.me/submissions/4ae1eaf8-b7a9-4c11-951d-9d8107b7830d

import Theorems.Thm_mme_dwz_table2_exact_outer_seven_eighths_has_nonhole

universe u v

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) {Copy : Type v} {Position : Type u}
    [Fintype Position] [DecidableEq Position]
    (outer : Copy → Position → Fin 15)
    (hProfile : ∀ j (s : Fin 15),
      Fintype.card {t : Position // outer j t = s} =
        MME.DWZTable2Counts.component s * m)
    (copy : ∀ j : Copy, MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hseven : ∀ j : Copy,
      7 * Fintype.card
          (MME.DWZTable2StandardForm.UsefulBlock m (outer j)) ≤
        8 * (copy j).nonholes.card) :
    ∃ small : ∀ j : Copy,
        MME.DWZTable2StandardForm.UsefulBlock m (outer j),
      ∀ j, small j ∈ (copy j).nonholes := by
  have hExists (j : Copy) :
      ∃ small : MME.DWZTable2StandardForm.UsefulBlock m (outer j),
        small ∈ (copy j).nonholes :=
    mme_dwz_table2_exact_outer_seven_eighths_has_nonhole
      m (outer j) (hProfile j) (copy j) (hseven j)
  choose small hsmall using hExists
  exact ⟨small, hsmall⟩
