-- Prove2me | solution 1 for mme_lower_half_ZMod_image_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:37:00.756507+00:00
-- url     : https://prove2.me/submissions/8671a953-7a91-4106-bf29-56af02d534a8

import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-- Natural labels in the lower half of a modulus remain distinct after
casting to residues. -/
theorem solution
    (p : ℕ) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (p / 2)) :
    (S.image (fun s : ℕ => (s : ZMod p))).card = S.card := by
  rw [Finset.card_image_iff]
  intro a ha b hb hab
  rw [ZMod.natCast_eq_natCast_iff'] at hab
  have ha_half := Finset.mem_range.mp (hSrange ha)
  have hb_half := Finset.mem_range.mp (hSrange hb)
  have ha_p : a < p := by omega
  have hb_p : b < p := by omega
  rwa [Nat.mod_eq_of_lt ha_p, Nat.mod_eq_of_lt hb_p] at hab
