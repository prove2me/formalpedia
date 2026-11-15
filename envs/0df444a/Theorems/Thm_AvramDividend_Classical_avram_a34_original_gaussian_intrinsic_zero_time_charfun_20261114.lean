-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a34_original_gaussian_intrinsic_zero_time_charfun_20261114
-- name    : AvramDividend.Classical.avram_a34_original_gaussian_intrinsic_zero_time_charfun_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:06:44.967197+00:00
-- url     : https://prove2.me/theorems/9234ee78-01f2-4dcb-9f6d-0c4425a98533
-- title:
--   Original physical intrinsic Gaussian residual has exact centred Gaussian characteristic function at time zero
-- statement:
--   For every original spectrally negative Lévy source and its genuine intrinsic Gaussian residual limit, the time-zero marginal of every conull-equivalent representative is the point mass at zero, with exactly the centred zero-variance Gaussian characteristic function.
-- source:
--   Proved A24 original globally adapted zero-start Gaussian representative; pinned Mathlib gaussianReal_zero_var.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a34_original_gaussian_intrinsic_zero_time_charfun_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ u : ℝ,
      charFun (P.map (G 0)) u =
        charFun (gaussianReal 0 0) u := by sorry
