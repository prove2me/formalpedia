-- Prove2me | Theorems.Thm_FCP_Transcendence_transcendental_e_mul_pi
-- name    : FCP.Transcendence.transcendental_e_mul_pi
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:54:31.357953+00:00
-- url     : https://prove2.me/theorems/9652fef3-a04a-4772-b7c4-b87d1aa3cda6
-- title:
--   Transcendence of $e\pi$
-- statement:
--   **Is $e\pi$ transcendental?** Stated here in the affirmative. This is one of the standard open questions on transcendence; it follows from Schanuel's conjecture, and the companion statement 'at least one of $\pi + e$ and $\pi e$ is transcendental' is an easy known theorem.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Transcendental.lean); https://en.wikipedia.org/wiki/Transcendental_number

import Mathlib

open Real

namespace FCP.Transcendence

theorem transcendental_e_mul_pi : Transcendental ℚ (exp 1 * π) := by sorry

end FCP.Transcendence
