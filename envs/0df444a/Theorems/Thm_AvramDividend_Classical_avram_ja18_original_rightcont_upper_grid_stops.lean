-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_rightcont_upper_grid_stops
-- name    : AvramDividend.Classical.avram_ja18_original_rightcont_upper_grid_stops
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:33:18.483385+00:00
-- url     : https://prove2.me/theorems/40599988-dfbb-4323-ae03-7883a9485029
-- title:
--   Bounded original stopping time admits finite-valued adapted upper meshes converging to the physical clock
-- statement:
--   Every bounded original right-continuous stopping time can be approximated from above by finite-valued stopping times on the same original right-continuous filtration, with each approximant bounded by the same deterministic horizon and converging pointwise to the original clock. The construction rounds to the next dyadic deterministic grid point; the already-Proved sampled-mesh ceiling theorem controls the one-mesh error.
-- source:
--   Genuinely independent clock-only child for 2d92580d. Reuse Proved 1d01e41f bounded sampled grid ceiling and 5bb5d001 adapted level events; prove real-clock IsStoppingTime via finite unions over grid events. No dividend reward, jump moments or auxiliary Brownian process.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_rightcont_upper_grid_stops
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (n : ℕ) (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ k ω : WithTop ℝ≥0))) ∧
      (∀ k, ∃ S : Finset ℝ≥0, ∀ ω, ρ k ω ∈ S) ∧
      (∀ k ω, τ ω ≤ ρ k ω) ∧
      (∀ k ω, ρ k ω ≤ (n : ℝ≥0)) ∧
      (∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (τ ω))) := by sorry
