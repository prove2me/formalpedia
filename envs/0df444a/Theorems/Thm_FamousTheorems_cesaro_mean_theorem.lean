-- Prove2me | Theorems.Thm_FamousTheorems_cesaro_mean_theorem
-- name    : FamousTheorems.cesaro_mean_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:20.293062+00:00
-- url     : https://prove2.me/theorems/ced505da-1b6d-40a4-98d6-3df073268a7c
-- title:
--   The Cesàro mean theorem
-- statement:
--   **The Cesàro mean theorem.** If a real sequence $u_n$ converges to $l$, then so do its averages:
--   $$\frac1n\sum_{i=0}^{n-1}u_i\;\longrightarrow\;l.$$
--
--   This is the basic regularity property of Cesàro summation. The converse fails (for example for $u_n=(-1)^n$), and that failure is what makes Cesàro summation useful, for instance in Fejér's theorem on Fourier series and in ergodic theory.
--
--   **Formalization note.** Mathlib's `Filter.Tendsto.cesaro`. The average at $n=0$ is $0^{-1}\cdot0=0$ in Lean, which does not affect the limit.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Filter.Tendsto.cesaro`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cesaro_mean_theorem {u : ℕ → ℝ} {l : ℝ} (h : Filter.Tendsto u Filter.atTop (nhds l)) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, u i) Filter.atTop (nhds l) := by sorry

end FamousTheorems
