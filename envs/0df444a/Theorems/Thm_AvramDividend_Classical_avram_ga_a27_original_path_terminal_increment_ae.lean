-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a27_original_path_terminal_increment_ae
-- name    : AvramDividend.Classical.avram_ga_a27_original_path_terminal_increment_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:43:23.47086+00:00
-- url     : https://prove2.me/theorems/85dd6f23-a961-40a5-8730-e92203dbc052
-- title:
--   Original zero-jump Lévy path terminal Gaussian increment tends to zero almost surely
-- statement:
--   For the actual original zero-jump spectrally negative Levy process, the last mesh increment X_n-X_(m*n/(m+1)) tends to zero almost surely. This follows from the proved path uniform continuity on [0,n], the proved rational-grid endpoint limit, and the path-continuity bridge. Needed in the horizon-boundary case of the clipped spatial Gaussian residual.
-- source:
--   Avram Gaussian A27 original process Brownian terminal increment

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a27_original_path_terminal_increment_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun m : ℕ =>
      X.X n ω - X.X ((m : ℝ≥0) * (n / ((m : ℝ≥0) + 1))) ω)
      atTop (nhds (0 : ℝ)) := by sorry
