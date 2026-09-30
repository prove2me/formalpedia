-- Prove2me | solution 1 for waring_cubes_mod_p
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:14:12.807512+00:00
-- url     : https://prove2.me/submissions/e4ecd254-e742-4a46-bd6f-66f401afe756

import Mathlib

set_option autoImplicit false

theorem solution (p : ℕ) (hp : Nat.Prime p) (h3 : 3 ∣ p - 1) :
    ∃ (g : ℕ) (_ : g ≤ 5), ∀ n : ZMod p,
      ∃ (xs : Fin g → ZMod p), n = ∑ i, xs i ^ 3 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp6 : ¬ p ∣ 6 := by
    intro h
    rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from h) with h | h
    · rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
      · exact hp.ne_one h
      · subst p
        norm_num at h3
    · rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
      · exact hp.ne_one h
      · subst p
        norm_num at h3
  have h6 : (6 : ZMod p) ≠ 0 := by
    exact fun h => hp6 ((ZMod.natCast_eq_zero_iff 6 p).mp h)
  refine ⟨4, by decide, ?_⟩
  intro n
  let x : ZMod p := n / 6
  refine ⟨![x + 1, x - 1, -x, -x], ?_⟩
  calc
    n = 6 * x := by
      dsimp [x]
      field_simp
    _ = _ := by
      norm_num [Fin.sum_univ_succ]
      ring

#print axioms solution
