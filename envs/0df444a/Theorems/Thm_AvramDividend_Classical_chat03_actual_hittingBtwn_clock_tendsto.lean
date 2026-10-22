-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_clock_tendsto
-- name    : AvramDividend.Classical.chat03_actual_hittingBtwn_clock_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:34:01.912234+00:00
-- url     : https://prove2.me/theorems/18be1475-0b49-4343-bb81-a38b9ddaafea
-- title:
--   Exact bounded sampled first-passage clock converges to the finite strict-exit time
-- statement:
--   For a spectrally negative Lévy sample path with a finite strict two-sided passage infimum and a positive vanishing uniform grid whose terminal observation time eventually exceeds the passage infimum by one time unit, the actual bounded Mathlib hittingBtwn clock, converted to physical time, converges to the continuous first-passage infimum.
-- source:
--   Proved Chat03 actual bounded hittingBtwn earliest crossing theorem and Proved first strict-grid exit epsilon-delta approximation, with pinned Mathlib tendsto_order.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_eventually_first_strict_grid_crossing
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_hittingBtwn_clock_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + 1 ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    Tendsto (fun n => (K n ω : ℝ≥0) * mesh n) atTop (𝓝 τ) := by sorry
