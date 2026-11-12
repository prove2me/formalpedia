-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb24_stopped_cash_limit_upper_from_two_noises
-- name    : AvramDividend.Classical.avram_jb24_stopped_cash_limit_upper_from_two_noises
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:23:56.543725+00:00
-- url     : https://prove2.me/theorems/a9d3f080-7aad-4d4a-be73-3f760547775e
-- title:
--   Original stopped cash finite-mesh inequality passes through two centred noise and vanishing-error limits
-- statement:
--   If every finite stopped mesh cash inequality is dominated by a deterministic initial reserve, the Gaussian gain, compensated-jump gain and an error term, then almost-sure convergence of the gains and vanishing of the error yield the same physical upper bound for the limiting cash reward.
-- source:
--   Pinned Lean ge_of_tendsto, conditional countable AE intersections and elementary Tendsto addition; necessary pathwise limit step for original ruin-clipped Ito cash ledger.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb24_stopped_cash_limit_upper_from_two_noises
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (b : ℝ) (F MG MJ : Ω → ℝ)
    (G J E : ℕ → Ω → ℝ)
    (hG : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hJ : ∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω)))
    (hE : ∀ᵐ ω ∂P, Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ)))
    (hUpper : ∀ k, ∀ᵐ ω ∂P,
      F ω ≤ b + G k ω + J k ω + E k ω) :
    ∀ᵐ ω ∂P, F ω ≤ b + MG ω + MJ ω := by sorry
