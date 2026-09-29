-- Prove2me | solution 1 for mme_CW_2376_exact_profile_induced_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:10:03.208048+00:00
-- url     : https://prove2.me/submissions/f74f045a-1361-49a2-ada7-3e9af5c96dce

import Theorems.Thm_mme_CW_2376_exact_profile_induced_hash_family
import Theorems.Thm_mme_CW_2376_profile_multinomial_rate_absorption

open MME Filter

theorem solution :
    ∀ᶠ m : ℕ in atTop,
      ∃ F : Finset (CW2376ExactProfileAddress m),
        CW2376InducedModeDisjoint F ∧
        (cw2376ProfileCountBase *
            Real.exp (-(cw2376ProfileRate m))) ^
            (cw2376ProfileLength m) ≤ (F.card : ℝ) := by
  filter_upwards
    [mme_CW_2376_exact_profile_induced_hash_family,
      mme_CW_2376_profile_multinomial_rate_absorption]
      with m hhash habsorb
  dsimp only at hhash habsorb
  obtain ⟨F, hF, hcount⟩ := hhash
  exact ⟨F, hF, habsorb.trans hcount⟩
