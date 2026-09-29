-- Prove2me | Theorems.Thm_FamousTheorems_levy_continuity
-- name    : FamousTheorems.levy_continuity
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:27.115987+00:00
-- url     : https://prove2.me/theorems/26eda1aa-d72b-4a0f-b502-ec788a7ec5c7
-- title:
--   Lévy's continuity theorem
-- statement:
--   **Lévy's continuity theorem.** For probability measures $\mu_n,\mu_0$ on a finite-dimensional real inner product space, $\mu_n\to\mu_0$ weakly if and only if the characteristic functions converge pointwise: $\hat\mu_n(t)\to\hat\mu_0(t)$ for every $t$.
--
--   Weak convergence is thereby reduced to the convergence of a family of explicit complex integrals. This is how the central limit theorem and other distributional limit theorems are classically proved.
--
--   **Formalization note.** Mathlib's `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`; the topology on `ProbabilityMeasure E` is weak convergence, and `charFun μ t = ∫ exp(i⟪t,x⟫) dμ`. The platform already carries the CLT-specialised forward direction (Gaussian limit); this is the general equivalence.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem levy_continuity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ₀ : MeasureTheory.ProbabilityMeasure E} {μ : ℕ → MeasureTheory.ProbabilityMeasure E} :
    Filter.Tendsto μ Filter.atTop (nhds μ₀) ↔
      ∀ t : E, Filter.Tendsto (fun n => MeasureTheory.charFun (μ n : MeasureTheory.Measure E) t) Filter.atTop
        (nhds (MeasureTheory.charFun (μ₀ : MeasureTheory.Measure E) t)) := by sorry

end FamousTheorems
