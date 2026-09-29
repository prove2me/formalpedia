-- Prove2me | Theorems.Thm_DeBruijnNewman_debruijn_newman_constant_nonneg
-- name    : DeBruijnNewman.debruijn_newman_constant_nonneg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T13:42:36.860088+00:00
-- url     : https://prove2.me/theorems/a5dad6cf-f790-4169-a742-2bcdcc8c9c6a
-- title:
--   Theorem 1 - the de Bruijn-Newman constant satisfies $\Lambda \ge 0$
-- statement:
--   Theorem 1 of the source: Newman's conjecture. The statement has two parts, asserted together:
--
--   1. $\Lambda \ge 0$, where $\Lambda$ is the infimum of the set of times $t$ for which every zero of $H_t$ is real;
--   2. every $t$ for which $H_t$ has only real zeros satisfies $t \ge 0$.
--
--   The second part is the content: it says that for no negative $t$ do all zeros of $H_t$ lie on the real axis. Since by Newman's theorem the set of admissible times is the ray $[\Lambda,\infty)$, the two parts express the same fact; stating both means the theorem does not rest on any convention for the infimum of a set that might be empty or unbounded below, and in particular cannot be satisfied by a junk value.
--
--   Combined with the Riemann hypothesis, which is the assertion $\Lambda \le 0$, this would give $\Lambda = 0$.
-- source:
--   B. Rodgers and T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020), e6, https://doi.org/10.1017/fmp.2020.6, Theorem 1, p. 3

import Mathlib
import Definitions.Def_DeBruijnNewman_core

namespace DeBruijnNewman

theorem debruijn_newman_constant_nonneg :
    0 ≤ Lambda ∧ ∀ t : ℝ, HasOnlyRealZeros t → 0 ≤ t := by sorry

end DeBruijnNewman
