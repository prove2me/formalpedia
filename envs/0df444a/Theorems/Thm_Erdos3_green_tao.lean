-- Prove2me | Theorems.Thm_Erdos3_green_tao
-- name    : Erdos3.green_tao
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:19:23.392002+00:00
-- url     : https://prove2.me/theorems/c606fccb-83b1-480a-ac0b-a68f3a284582
-- title:
--   Green–Tao theorem
-- statement:
--   **Green–Tao theorem.** The primes contain arithmetic progressions of every finite length. Since $\sum_p 1/p=\infty$ (Euler), this is the special case $A=\{\text{primes}\}$ of the goal, and it was the case that Erdős's conjecture was most famously expected to cover.
-- source:
--   B. Green and T. Tao, *The primes contain arbitrarily long arithmetic progressions*, Ann. of Math. 167 (2008), 481–547, Theorem 1.1; cited at https://www.erdosproblems.com/3

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos3
open Erdos142

theorem green_tao : ∀ k : ℕ, ∃ S ⊆ {p : ℕ | p.Prime}, IsAPOfLength S k := by
  sorry

end Erdos3
