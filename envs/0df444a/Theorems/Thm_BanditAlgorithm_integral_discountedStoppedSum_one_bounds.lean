-- Prove2me | Theorems.Thm_BanditAlgorithm_integral_discountedStoppedSum_one_bounds
-- name    : BanditAlgorithm.integral_discountedStoppedSum_one_bounds
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T04:06:15.591623+00:00
-- url     : https://prove2.me/theorems/1383a38d-0a45-4302-8958-4e478c8ed8ce
-- title:
--   Bounds on expected discounted stopping duration
-- statement:
--   If an admissible stopping rule plays for at least one round, its expected discounted duration lies between $1$ and the full geometric duration $\sum_{t\geq0}\alpha^t$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), denominator in Eq. (35.9), printed p.448.

import Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum_one

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.integral_discountedStoppedSum_one_bounds
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (x : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ)
    (hτ1 : ∀ ω, 1 ≤ τ ω) :
    1 ≤ (∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
      ∂markovChainMeasure P x) ∧
    (∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
      ∂markovChainMeasure P x) ≤ ∑' t : ℕ, α ^ t := by
  sorry
