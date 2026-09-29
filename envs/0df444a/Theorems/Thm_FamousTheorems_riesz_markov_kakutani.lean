-- Prove2me | Theorems.Thm_FamousTheorems_riesz_markov_kakutani
-- name    : FamousTheorems.riesz_markov_kakutani
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:54.300415+00:00
-- url     : https://prove2.me/theorems/b81e8289-571d-49ef-8f76-db0552b292ca
-- title:
--   The Riesz–Markov–Kakutani representation theorem (existence)
-- statement:
--   **The Riesz–Markov–Kakutani representation theorem (existence).** Let $X$ be a locally compact Hausdorff space with its Borel σ-algebra, and $\Lambda$ a positive linear functional on the space $C_c(X)$ of compactly supported continuous real functions. Then there is a regular Borel measure $\mu$ on $X$ with
--   $$\Lambda(f)=\int_Xf\,d\mu\qquad\text{for all } f\in C_c(X).$$
--
--   The theorem identifies positive functionals on continuous functions with measures. It is one of the foundations of modern measure theory and functional analysis, and one standard route to constructing Lebesgue and Haar measure. It also identifies the dual of $C_0(X)$ with the space of finite signed regular measures.
--
--   **Formalization note.** Mathlib's `RealRMK.integral_rieszMeasure`, with regularity from the instance `RealRMK.regular_rieszMeasure`. The witness is Mathlib's measure `RealRMK.rieszMeasure Λ`. `CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ` is the type of positive linear maps. Uniqueness among regular measures is a separate Mathlib result and is not part of this statement.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `RealRMK.integral_rieszMeasure`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem riesz_markov_kakutani {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (Λ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ) :
    ∃ μ : MeasureTheory.Measure X, μ.Regular ∧
      ∀ f : CompactlySupportedContinuousMap X ℝ, ∫ x, f x ∂μ = Λ f := by sorry

end FamousTheorems
