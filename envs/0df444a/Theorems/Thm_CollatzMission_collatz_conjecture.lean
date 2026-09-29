-- Prove2me | Theorems.Thm_CollatzMission_collatz_conjecture
-- name    : CollatzMission.collatz_conjecture
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-08T04:53:49.281348+00:00
-- url     : https://prove2.me/theorems/661c9a38-220b-49a9-918a-6e837e45a7cd
-- title:
--   Collatz conjecture
-- statement:
--   **Collatz Conjecture** (3n+1 Problem): Starting from any positive integer $n$, the iteration $f(n) = n/2$ (if $n$ even) or $f(n) = 3n+1$ (if $n$ odd) eventually reaches 1.
--
--   Example: $6 \to 3 \to 10 \to 5 \to 16 \to 8 \to 4 \to 2 \to 1$.
--
--   Proposed by Lothar Collatz in 1937. Verified for all integers up to $2^{68}$. Tao (2019) proved almost all orbits reach arbitrarily small values. Erdős said 'Mathematics is not yet ready for such problems'.
--
--   **Formalization Note** The Collatz step is imported from the reusable `collatzStepMap` definition module so that proof submissions can be checked.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture

import Mathlib
import Definitions.Def_collatzStepMap

namespace CollatzMission

theorem collatz_conjecture (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, collatzStep^[m] n = 1 := by
  sorry

end CollatzMission
