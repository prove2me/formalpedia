-- Prove2me | Theorems.Thm_FamousTheorems_euler_identity
-- name    : FamousTheorems.euler_identity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:22.037975+00:00
-- url     : https://prove2.me/theorems/dfeb7cae-e3e1-428e-aecd-1067bc81c098
-- title:
--   Euler's identity e^{iπ} = −1
-- statement:
--   **Euler's identity.**
--   $$e^{i\pi}=-1.$$
--
--   This is the special case $\theta=\pi$ of Euler's formula $e^{i\theta}=\cos\theta+i\sin\theta$. It connects the constants $e$, $i$, $\pi$ and $1$, and it is often cited as the most celebrated formula in mathematics.
--
--   **Formalization note.** Mathlib's `Complex.exp_pi_mul_I`. `Complex.exp` is the complex exponential and `Real.pi` is cast to `ℂ`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Complex.exp_pi_mul_I`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_identity : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := by sorry

end FamousTheorems
