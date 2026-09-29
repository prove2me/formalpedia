-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_profile_exact_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:29:00.889417+00:00
-- url     : https://prove2.me/submissions/51c001f2-c400-4f68-bc47-a5b9d931cb96

import Mathlib.Tactic
import Theorems.Thm_mme_CW_q6_exact_coupled_address_regularity

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N L G : ℕ) (hLG : L + G = N) :
    (cwQ6ExactXWords N L G).card *
          (cwQ6ExactYWords N L G).card *
          (cwQ6ExactZWords N L G).card =
        Nat.choose (2 * N) N ^ (2 : ℕ) *
          (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) ∧
      ∀ x ∈ cwQ6ExactXWords N L G,
        ∀ y ∈ cwQ6ExactYWords N L G,
          ∀ z ∈ cwQ6ExactZWords N L G,
            ((cwQ6ExactAddresses N L G).filter
                  (fun e ↦ e 0 = x)).card *
                ((cwQ6ExactAddresses N L G).filter
                  (fun e ↦ e 1 = y)).card *
                ((cwQ6ExactAddresses N L G).filter
                  (fun e ↦ e 2 = z)).card =
              Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
  have hregular := mme_CW_q6_exact_coupled_address_regularity N L G hLG
  constructor
  · rw [hregular.x_word_card, hregular.y_word_card,
      hregular.z_word_card]
    ring
  · intro x hx y hy z hz
    rw [hregular.x_degree x hx, hregular.y_degree y hy,
      hregular.z_degree z hz]
    ring
