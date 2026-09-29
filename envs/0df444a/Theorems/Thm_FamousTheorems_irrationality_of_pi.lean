-- Prove2me | Theorems.Thm_FamousTheorems_irrationality_of_pi
-- name    : FamousTheorems.irrationality_of_pi
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:19.014567+00:00
-- url     : https://prove2.me/theorems/3858e0a3-10b9-413f-b0aa-193d1aa459b8
-- title:
--   Irrationality of π
-- statement:
--   **Irrationality of $\pi$.** The number $\pi$ is irrational.
--
--   Lambert proved this in 1761 using continued fractions, and simpler proofs were later given by Hermite and Niven. It was a step toward Lindemann's 1882 theorem that $\pi$ is transcendental, which settled the ancient problem of squaring the circle in the negative.
--
--   **Formalization note.** Mathlib's `irrational_pi`. `Irrational x` means that $x$ is not in the range of the cast `ℚ → ℝ`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `irrational_pi`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem irrationality_of_pi : Irrational Real.pi := by sorry

end FamousTheorems
