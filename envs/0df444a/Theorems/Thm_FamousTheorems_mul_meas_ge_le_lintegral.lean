-- Prove2me | Theorems.Thm_FamousTheorems_mul_meas_ge_le_lintegral
-- name    : FamousTheorems.mul_meas_ge_le_lintegral
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:26.501176+00:00
-- url     : https://prove2.me/theorems/02b9408a-b966-4b18-962c-aad1c8a6502d
-- title:
--   Markov's inequality
-- statement:
--   **Markov's inequality.** For a nonnegative measurable $f$ and $\varepsilon > 0$, $$\varepsilon \cdot \mu\{x : f(x) \ge \varepsilon\} \le \int f \,d\mu.$$ A nonnegative function cannot be large on a large set without having a large integral. The bound uses nothing but nonnegativity — no independence, no moments, no distributional assumptions — which is why it is the starting point for nearly every concentration estimate. Applying it to $|X - \mathbb{E}X|^2$ gives Chebyshev's inequality, and to $e^{tX}$ gives the Chernoff bound; the whole hierarchy of tail estimates is Markov applied to a cleverly chosen nonnegative function. **Formalization note.** The integral is the lower Lebesgue integral of an `ℝ≥0∞`-valued function, so no integrability hypothesis is needed. The result is Mathlib's `MeasureTheory.mul_meas_ge_le_lintegral`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem mul_meas_ge_le_lintegral :
    ∀ {α : Type u_1} {mα : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
    {f : α → ENNReal}, Measurable f → ∀ (ε : ENNReal), ε * μ {x | ε ≤ f x} ≤ ∫⁻ (a : α), f a ∂μ := by sorry

end FamousTheorems
