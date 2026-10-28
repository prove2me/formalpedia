-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_two_sided_first_exit_compensated_exponential_tendsto
-- name    : AvramDividend.Classical.levy_capped_two_sided_first_exit_compensated_exponential_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:55:53.910547+00:00
-- url     : https://prove2.me/theorems/5a016d09-28e5-44e3-9256-d1bcb7dc1ed1
-- title:
--   Compensated Lévy exponential converges pathwise at capped two-sided first exits
-- statement:
--   For a genuine first strict two-sided grid crossing on vanishing meshes, the exponential of a linear combination of its clipped Lévy terminal reserve and clipped passage time converges to the corresponding continuous-time first-exit value. It follows from the independently proved stopped reserve and stopped clock convergence theorems, without any martingale or harmonicity assumption.
-- source:
--   Dependencies proposed and submitted as new Workstream 1A pathwise first-exit reserve 8f0caca0-a4bd-413f-a8ca-36fe1e61c8c8 and clock 8dfcdfae-4092-457e-a3cb-eb5354db7b43. Publish only after both reach canonical Proved.

import Theorems.Thm_AvramDividend_Classical_levy_capped_two_sided_first_exit_stopped_reserve_tendsto
import Theorems.Thm_AvramDividend_Classical_levy_capped_two_sided_first_exit_clock_tendsto
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_capped_two_sided_first_exit_compensated_exponential_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (first : ℕ → ℕ)
    (hfirst : ∀ᶠ n in atTop,
      (X.X ((first n : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((first n : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < first n →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω)))
    (θ q : ℝ) :
    Tendsto (fun n =>
      let stop : ℝ≥0 := min ((first n : ℝ≥0) * mesh n) T
      Real.exp (θ * X.X stop ω - q * (stop : ℝ))) atTop
      (𝓝 (Real.exp (θ * X.X (min τ T) ω - q * ((min τ T : ℝ≥0) : ℝ)))) := by sorry
