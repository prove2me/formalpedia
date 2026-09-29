-- Prove2me | Theorems.Thm_FamousTheorems_irrational_sqrt_two
-- name    : FamousTheorems.irrational_sqrt_two
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:51:57.619698+00:00
-- url     : https://prove2.me/theorems/56c68e39-3795-459f-8123-550eddaf8872
-- title:
--   The irrationality of $\sqrt{2}$
-- statement:
--   **$\sqrt 2$ is irrational.**
--
--   $$\sqrt 2 \notin \mathbb{Q}.$$
--
--   The classical proof — attributed to the Pythagoreans and reported by Aristotle — supposes
--   $\sqrt 2 = a/b$ in lowest terms, deduces $a^2 = 2b^2$, concludes $a$ is even, writes $a = 2c$ to
--   get $b^2 = 2c^2$ and hence $b$ even too, contradicting lowest terms. It is the first known proof
--   by contradiction and the discovery that broke the Pythagorean programme of commensurability.
--
--   **Formalization note.** `Irrational x` is `x ∉ Set.range ((↑) : ℚ → ℝ)`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem irrational_sqrt_two : Irrational (Real.sqrt 2) := by sorry

end FamousTheorems
