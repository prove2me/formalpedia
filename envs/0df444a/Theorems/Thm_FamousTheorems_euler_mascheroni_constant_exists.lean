-- Prove2me | Theorems.Thm_FamousTheorems_euler_mascheroni_constant_exists
-- name    : FamousTheorems.euler_mascheroni_constant_exists
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:37:12.307699+00:00
-- url     : https://prove2.me/theorems/6149c70a-35fe-408d-95d8-18fbe265c522
-- title:
--   Existence of the Euler–Mascheroni constant
-- statement:
--   **Existence of the Euler–Mascheroni constant.** The sequence
--   $$H_n-\log n=1+\frac12+\cdots+\frac1n-\log n$$
--   converges to a real limit $\gamma$.
--
--   The limit $\gamma\approx0.5772$ is the Euler–Mascheroni constant. It measures how far the harmonic series is from the logarithm, and it appears in the Laurent expansion of $\zeta$ at $s=1$, the derivative $\Gamma'(1)=-\gamma$ and Mertens' theorems. It is not even known whether $\gamma$ is irrational.
--
--   **Formalization note.** Mathlib's `Real.tendsto_harmonic_sub_log`, which proves that the limit is `Real.eulerMascheroniConstant`. The statement is the existence of the limit. `harmonic n` is the rational number $H_n$ (with $H_0=0$), cast to $\mathbb R$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.tendsto_harmonic_sub_log`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem euler_mascheroni_constant_exists : ∃ γ : ℝ, Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) Filter.atTop (nhds γ) := by sorry

end FamousTheorems
