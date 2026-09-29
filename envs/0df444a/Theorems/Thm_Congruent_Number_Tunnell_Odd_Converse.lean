-- Prove2me | Theorems.Thm_Congruent_Number_Tunnell_Odd_Converse
-- name    : Congruent_Number_Tunnell_Odd_Converse
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-06-25T18:46:29.494697+00:00
-- url     : https://prove2.me/theorems/c5c8ddd7-400b-48c1-a6c3-f68a88d93a63
-- statement:
--   **Tunnell's theorem — converse, odd case (conditional on BSD).** For squarefree odd $n$: if $2\,|A_n| = |B_n|$, where $A_n=\{(x,y,z)\in\mathbb{Z}^3 : n=2x^2+y^2+32z^2\}$ and $B_n=\{(x,y,z) : n=2x^2+y^2+8z^2\}$, then $n$ is a congruent number (the area of a rational right triangle). (Statement following the DeepMind formal-conjectures library.)
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/CongruentNumber.lean

import Mathlib

def congruentNumberDM (n : ℕ) : Prop :=
  ∃ a b c : ℚ, a ^ 2 + b ^ 2 = c ^ 2 ∧ (n : ℚ) = (2⁻¹ : ℚ) * a * b

def A_DM (n : ℕ) : Set (ℤ × ℤ × ℤ) := {(x, y, z) | (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2}
def B_DM (n : ℕ) : Set (ℤ × ℤ × ℤ) := {(x, y, z) | (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2}

theorem Congruent_Number_Tunnell_Odd_Converse (n : ℕ) (hsqf : Squarefree n) (hodd : Odd n) :
    2 * (A_DM n).ncard = (B_DM n).ncard → congruentNumberDM n := by sorry
