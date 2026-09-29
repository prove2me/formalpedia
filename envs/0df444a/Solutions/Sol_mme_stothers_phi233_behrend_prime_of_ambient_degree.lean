-- Prove2me | solution 1 for mme_stothers_phi233_behrend_prime_of_ambient_degree
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T02:42:23.411712+00:00
-- url     : https://prove2.me/submissions/eb72ca9c-c454-4c5b-9a8c-9b16f1ea14c8

import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_ambient_star_crude_bounds
import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
import Theorems.Thm_mme_stothers_phi233_lower_half_cast_label_package

open MME BigOperators

set_option autoImplicit false

theorem solution
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress N alpha beta gamma delta) :
    ∃ p : ℕ, Nat.Prime p ∧ 7 ≤ p ∧
      ∃ S : Finset (ZMod p),
        (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
          x + y = 2 * z → x = z ∧ z = y) ∧
        6 *
            ((∏ l : Fin 3,
              Nat.card
                {b : MME.StothersFourth.Phi233.MarginalAddress
                    N alpha beta gamma delta //
                  b.1 l = a.1.1 l}) : ℝ) ≤
          (S.card : ℝ) ∧
        (p : ℝ) ≤
          ((∏ l : Fin 3,
              Nat.card
                {b : MME.StothersFourth.Phi233.MarginalAddress
                    N alpha beta gamma delta //
                  b.1 l = a.1.1 l}) : ℝ) *
            Real.exp (2000 * Real.sqrt (((18 * N + 1 : ℕ) : ℝ))) := by
  classical
  let D := ∏ l : Fin 3,
    Nat.card {b : MME.StothersFourth.Phi233.MarginalAddress
      N alpha beta gamma delta // b.1 l = a.1.1 l}
  obtain ⟨hD1, hD5⟩ :=
    mme_stothers_phi233_ambient_star_crude_bounds N alpha beta gamma delta a
  obtain ⟨p, hp, hp5, S, hSr, hSf, hSbig, hpbound⟩ :=
    mme_prime_behrend_dominates_bounded_collision_degree (18 * N) D hD1 hD5
  have hcard := Finset.card_le_card hSr
  rw [Finset.card_range] at hcard
  have hScard : 6 * D ≤ S.card := by exact_mod_cast hSbig
  have hp7 : 7 ≤ p := by omega
  obtain ⟨hcastcard, hcastfree⟩ :=
    mme_stothers_phi233_lower_half_cast_label_package p S hSr hSf
  refine ⟨p, hp, hp7, S.image (fun s : ℕ => (s : ZMod p)), hcastfree, ?_, ?_⟩
  · simpa only [hcastcard, D, Nat.cast_prod] using hSbig
  · simpa only [D, Nat.cast_prod] using hpbound
