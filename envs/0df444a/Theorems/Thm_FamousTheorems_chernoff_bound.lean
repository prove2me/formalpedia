-- Prove2me | Theorems.Thm_FamousTheorems_chernoff_bound
-- name    : FamousTheorems.chernoff_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:51.692821+00:00
-- url     : https://prove2.me/theorems/0e6307dc-49ab-4ad1-9001-33dcb07faad4
-- title:
--   The Chernoff bound
-- statement:
--   **The Chernoff bound.** Let $X$ be a real random variable on a finite measure space, $t\ge0$, and suppose $e^{tX}$ is integrable. Then for every real $\varepsilon$,
--   $$\mu\{X\ge\varepsilon\}\le e^{-t\varepsilon}\,M_X(t),\qquad M_X(t)=\int e^{tX}\,d\mu.$$
--
--   Optimising over $t$ gives exponentially small tail bounds. This is the starting point of large deviations theory (Cramér's theorem) and of the concentration inequalities of Hoeffding and Bernstein type used throughout probability, statistics and the analysis of randomized algorithms.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.measure_ge_le_exp_mul_mgf`. `mgf X μ t` is the moment generating function $\int e^{tX}\,d\mu$ and `μ.real` is the measure as a real number. The inequality is Markov's inequality applied to $e^{tX}$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.measure_ge_le_exp_mul_mgf`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory

theorem chernoff_bound {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω} {t : ℝ} [IsFiniteMeasure μ]
    (ε : ℝ) (ht : 0 ≤ t) (h_int : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * mgf X μ t := by sorry

end FamousTheorems
