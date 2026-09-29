-- Prove2me | solution 1 for eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/b3e488b2-e1fb-5f38-9ee7-e8b2a1a216d7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero

set_option autoImplicit false

namespace ARITHPROG

theorem main {R : Type*} [CommRing R] (e : ℕ) (a : ℕ → R)
    (h : ∀ k : ℕ, k + 1 < e → a k - 2 * a (k + 1) + a (k + 2) = 0) :
    ∀ n : ℕ, n + 1 ≤ e →
      a n = a 0 + (a 1 - a 0) * n ∧ a (n + 1) = a 0 + (a 1 - a 0) * (n + 1 : ℕ) := by
  intro n
  induction n with
  | zero =>
    intro _
    constructor <;> simp
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega)
    refine ⟨h2, ?_⟩
    have h3 := h n (by omega)
    push_cast at h1 h2 ⊢
    linear_combination h3 - h1 + 2 * h2

end ARITHPROG

theorem solution
    {R : Type*} [CommRing R] (e : ℕ) (a : ℕ → R)
    (h : ∀ k : ℕ, k + 1 < e → a k - 2 * a (k + 1) + a (k + 2) = 0)
    (k : ℕ) (hk : k ≤ e) :
    a k = a 0 + (a 1 - a 0) * k := by
  rcases k with _ | n
  · simp
  · exact (ARITHPROG.main e a h n hk).2

end S_eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero
end P2MW
export P2MW.S_eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero (solution)
