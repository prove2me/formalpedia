-- Prove2me | Theorems.Thm_FCP_Transcendence_transcendental_pi_add_e_or_pi_mul_e
-- name    : FCP.Transcendence.transcendental_pi_add_e_or_pi_mul_e
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T20:54:44.826225+00:00
-- url     : https://prove2.me/theorems/10c1cd9b-487e-4e9a-8e99-138fae9cacac
-- title:
--   At least one of $\pi + e$, $\pi e$ is transcendental
-- statement:
--   **A known warm-up.** At least one of $\pi + e$ and $\pi e$ is transcendental. Indeed, if both were algebraic, then $\pi$ and $e$ would be roots of the quadratic $X^2 - (\pi+e)X + \pi e$ over $\overline{\mathbb{Q}}$ and hence algebraic, contradicting the Lindemann--Weierstrass theorem. This is the elementary anchor of the transcendence group and a realistic formalization target.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Transcendental.lean); https://en.wikipedia.org/wiki/Transcendental_number

import Mathlib

open Real

namespace FCP.Transcendence

theorem transcendental_pi_add_e_or_pi_mul_e :
    Transcendental ℚ (π + exp 1) ∨ Transcendental ℚ (π * exp 1) := by sorry

end FCP.Transcendence
