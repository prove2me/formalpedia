-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_original_BV_finite_activity_jump_sum_exact
-- name    : AvramDividend.Classical.avram_bva20_original_BV_finite_activity_jump_sum_exact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T23:31:19.291241+00:00
-- url     : https://prove2.me/theorems/69dc5e14-c06b-469b-9733-ef28d56baaa4
-- title:
--   Original finite-activity BV Lévy path equals drift plus the sum of its actual jumps
-- statement:
--   For the original spectrally negative Lévy process, bounded variation and finite negative-jump activity imply that, almost surely, the drift residual on every compact positive time interval equals the cumulative sum of the actual negative jump losses. This is a source-exact finite-activity step-path representation needed in the original stopped dividend cash ledger. It is to be derived from the previously Proved finite-range residual, finite jump-time, and continuous jump-removed residual results, never from a newly constructed auxiliary process. Intended dependency of the root-connected physical cell theorem 30da2b68-6242-4d6b-8dc4-c85336ffcaee.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva20_original_BV_finite_activity_jump_sum_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) * X.drift - X.X t ω =
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by sorry
