-- Prove2me | Theorems.Thm_FCP_Mersenne_catalan_mersenne_conjecture
-- name    : FCP.Mersenne.catalan_mersenne_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:48:31.46179+00:00
-- url     : https://prove2.me/theorems/cd467562-a719-4a34-908d-543b94968a5c
-- title:
--   Catalan--Mersenne conjecture: $c_n$ is prime for all $n \ge 5$
-- statement:
--   **Catalan--Mersenne conjecture.** Let $c_0 = 2$ and $c_{n+1} = 2^{c_n} - 1$, so that $c_1 = 3$, $c_2 = 7$, $c_3 = 127$, $c_4 = 2^{127}-1$. The first five terms are known to be prime; Catalan asked whether the sequence continues to consist of primes. The statement here is the affirmative form for all $n \ge 5$; $c_5$ has more than $10^{37}$ digits and its primality is far beyond reach, and many authors expect the answer to be negative.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Mersenne.lean); https://mathworld.wolfram.com/Catalan-MersenneNumber.html

import Mathlib
import Definitions.Def_FCP_Mersenne

namespace FCP.Mersenne

theorem catalan_mersenne_conjecture (n : ℕ) (hn : 5 ≤ n) : Nat.Prime (catalanMersenne n) := by
  sorry

end FCP.Mersenne
