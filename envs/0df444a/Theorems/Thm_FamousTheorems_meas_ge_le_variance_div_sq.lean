-- Prove2me | Theorems.Thm_FamousTheorems_meas_ge_le_variance_div_sq
-- name    : FamousTheorems.meas_ge_le_variance_div_sq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:27.153977+00:00
-- url     : https://prove2.me/theorems/86be7df4-1c57-454b-be95-9a620f48b93d
-- title:
--   Chebyshev's inequality
-- statement:
--   **Chebyshev's inequality.** For a random variable with finite variance and $c > 0$, $$\mathbb{P}\bigl(|X - \mathbb{E}X| \ge c\bigr) \le \frac{\operatorname{Var}(X)}{c^2}.$$ The variance controls how far a random variable can stray from its mean: deviations of size $c$ have probability at most $\operatorname{Var}(X)/c^2$. The bound is distribution-free, requiring only a finite second moment, and it is sharp in that generality — two-point distributions attain it. It is the quantitative content behind the weak law of large numbers: averaging $n$ independent copies divides the variance by $n$, so the deviation probability vanishes. **Formalization note.** `Var[X]` is the variance under a probability measure, and the hypothesis is membership in $L^2$. The result is Mathlib's `ProbabilityTheory.meas_ge_le_variance_div_sq`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem meas_ge_le_variance_div_sq :
    ∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} 
    [MeasureTheory.IsFiniteMeasure μ] {X : Ω → ℝ}, 
    MeasureTheory.MemLp X 2 μ → 
    ∀ {c : ℝ}, 0 < c → μ {ω | c ≤ |X ω - ∫ (x : Ω), X x ∂μ|} ≤ ENNReal.ofReal (ProbabilityTheory.variance X μ / c ^ 2) := by sorry

end FamousTheorems
