-- Prove2me | Theorems.Thm_FamousTheorems_lintegral_mul_le_lp_mul_lq
-- name    : FamousTheorems.lintegral_mul_le_lp_mul_lq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:13.540593+00:00
-- url     : https://prove2.me/theorems/08cbd5db-cecc-4d86-9258-4924065285ad
-- title:
--   Hölder's inequality
-- statement:
--   **H\u00f6lder's inequality.** For conjugate exponents $1/p + 1/q = 1$, $$\int |fg| \;\le\; \lVert f\rVert_p \,\lVert g\rVert_q.$$ Taking $p = q = 2$ recovers Cauchy\u2013Schwarz; the general case is what makes the whole scale of $L^p$ spaces usable. The inequality is exactly the statement that $L^q$ embeds in the dual of $L^p$, and it is sharp — equality holds when $|f|^p$ and $|g|^q$ are proportional. Its consequences include Minkowski's inequality (hence that $\lVert\cdot\rVert_p$ is a norm at all), interpolation between $L^p$ spaces, and most of the estimates in the theory of partial differential equations. The underlying mechanism is Young's inequality $ab \le a^p/p + b^q/q$, itself convexity of the exponential. **Formalization note.** The integrals are lower Lebesgue integrals of `ℝ≥0∞`-valued functions, so no integrability hypotheses are needed. The result is Mathlib's `NNReal.lintegral_mul_le_Lp_mul_Lq`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem lintegral_mul_le_lp_mul_lq :
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
    {p q : ℝ}, 
    p.HolderConjugate q → 
    ∀ {f g : α → NNReal}, 
    AEMeasurable f μ → 
    AEMeasurable g μ → 
    ∫⁻ (a : α), ↑((f * g) a) ∂μ ≤ (∫⁻ (a : α), ↑(f a) ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), ↑(g a) ^ q ∂μ) ^ (1 / q) := by sorry

end FamousTheorems
