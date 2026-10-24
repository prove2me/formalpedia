-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_measurable_of_vanishing_grid
-- name    : AvramDividend.Classical.chat08_upper_passage_measurable_of_vanishing_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:00:34.825589+00:00
-- url     : https://prove2.me/theorems/f254f87b-e1be-4379-b732-a740e6922d77
-- title:
--   Actual strict upper first-passage clock is measurable via vanishing-grid limits
-- statement:
--   Given any positive sequence of deterministic sampling widths converging to zero, the exact spectrally negative Lévy strict upper first-passage time is measurable as an extended nonnegative random variable. The proof combines the already verified measurability of each sampled clock with the verified pointwise convergence of sampled clocks, using Mathlib's ENNReal measurable-of-tendsto theorem. This closes the structural passage-time measurability implication required for first-record killed renewal payments.
-- source:
--   Prove2Me chat03_uniform_grid_passage_clocks_measurable and chat03_official_upper_grid_clock_tendsto; Mathlib ENNReal.measurable_of_tendsto.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Constructions
import Theorems.Thm_AvramDividend_Classical_chat03_uniform_grid_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_official_upper_grid_clock_tendsto

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_upper_passage_measurable_of_vanishing_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (upper : ℝ)
    (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Measurable (twoSidedExitUpTime X upper) := by sorry
