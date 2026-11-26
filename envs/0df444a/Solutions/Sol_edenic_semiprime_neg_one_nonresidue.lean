-- Prove2me | solution 1 for edenic_semiprime_neg_one_nonresidue
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-26T11:33:53.675708+00:00
-- url     : https://prove2.me/submissions/67d9f6e5-c83a-4323-94bd-2bc73b930063

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ¬∃ y : ZMod n, y ^ 2 = -1 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hne2
  have hodd : p % 2 = 1 := by omega
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hex : ∃ q, q.Prime ∧ q ∣ p * (p + 2) ∧ q % 4 = 3 := by
    rcases h4 with h4 | h4
    · exact ⟨p + 2, hp2, ⟨p, by ring⟩, by omega⟩
    · exact ⟨p, hp, ⟨p + 2, rfl⟩, h4⟩
  obtain ⟨q, hq, hqn, hq4⟩ := hex
  intro hy
  obtain ⟨y, hy⟩ := hy
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨z, hz⟩ := ZMod.isSquare_neg_one_of_dvd hqn ⟨y, by rw [← pow_two]; exact hy.symm⟩
  have hz2 : z ^ 2 = -1 := by rwa [pow_two, eq_comm]
  exact absurd (ZMod.mod_four_ne_three_of_sq_eq_neg_one hz2) (by omega)
