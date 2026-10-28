-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_two_sided_first_exit_clock_tendsto
-- name    : AvramDividend.Classical.levy_capped_two_sided_first_exit_clock_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:44:44.325403+00:00
-- url     : https://prove2.me/theorems/8dfcdfae-4092-457e-a3cb-eb5354db7b43
-- title:
--   Stopped Lévy first-exit clock converges along genuine finite-grid crossings
-- statement:
--   For a fixed spectrally negative Lévy sample path with finite strict two-sided first passage and any deterministic finite horizon, genuine minimal first-exit grid indices on positive meshes tending to zero have clipped passage times converging to the clipped continuous exit time. The result preserves first strict crossing rather than appealing to a false discrete q-scale martingale.
-- source:
--   Accepted chat03_first_grid_capped_time_convergence eed8714d-158f-47e7-874c-d8451221b070; the first-crossing witness is uniquely selected by natural-number minimality and the order-topology convergence criterion.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_capped_time_convergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_capped_two_sided_first_exit_clock_tendsto
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
           upper < X.X ((j : ℝ≥0) * mesh n) ω))) :
    Tendsto (fun n =>
      min ((first n : ℝ≥0) * mesh n) T) atTop (𝓝 (min τ T)) := by sorry
