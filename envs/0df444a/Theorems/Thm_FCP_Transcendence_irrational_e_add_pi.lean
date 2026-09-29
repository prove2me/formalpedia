-- Prove2me | Theorems.Thm_FCP_Transcendence_irrational_e_add_pi
-- name    : FCP.Transcendence.irrational_e_add_pi
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:54:17.944696+00:00
-- url     : https://prove2.me/theorems/f41e8a4b-1f1e-4bcb-a756-1f36ef322253
-- title:
--   Irrationality of $e + \pi$
-- statement:
--   **Is $e + \pi$ irrational?** Stated here in the affirmative. Although $e$ and $\pi$ are both transcendental, nothing is known about $e + \pi$: it is not even known to be irrational. What *is* known is that $e + \pi$ and $e\pi$ cannot both be algebraic, since $e$ and $\pi$ are the roots of $X^2 - (e+\pi)X + e\pi$.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Irrational.lean); https://en.wikipedia.org/wiki/Irrational_number#Open_questions

import Mathlib

open Real

namespace FCP.Transcendence

theorem irrational_e_add_pi : Irrational (exp 1 + π) := by sorry

end FCP.Transcendence
