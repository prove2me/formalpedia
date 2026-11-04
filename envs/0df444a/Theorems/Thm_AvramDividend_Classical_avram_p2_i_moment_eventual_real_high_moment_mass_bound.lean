-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_eventual_real_high_moment_mass_bound
-- name    : AvramDividend.Classical.avram_p2_i_moment_eventual_real_high_moment_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:46:26.986215+00:00
-- url     : https://prove2.me/theorems/9245229d-4b7c-4158-9b2a-78352527a415
-- title:
--   High moments of approximating finite measures are eventually bounded by limiting mass
-- statement:
--   For a general filter of approximating finite real measures, suppose the real kth moments converge to those of a measure concentrated on [0,1]. Then for every positive epsilon the approximating kth moments are eventually at most the limiting total mass plus epsilon. The bound is independent of the chosen exponent, apart from how far along the filter one must go, and directly controls the high-power tail beyond z=2.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_i_moment_eventual_real_high_moment_mass_bound
    {ι : Type*} (l : Filter ι) (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hμ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hOne : Integrable (fun _ : ℝ => (1 : ℝ)) μ)
    (k : ℕ) (hk : Integrable (fun z : ℝ => z ^ k) μ)
    (hmom : Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
      (nhds (∫ z : ℝ, z ^ k ∂μ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in l, (∫ z : ℝ, z ^ k ∂μi i) <
      (∫ _ : ℝ, (1 : ℝ) ∂μ) + ε := by sorry
