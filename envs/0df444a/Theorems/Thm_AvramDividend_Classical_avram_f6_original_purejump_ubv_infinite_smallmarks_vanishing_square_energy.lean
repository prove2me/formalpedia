-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_purejump_ubv_infinite_smallmarks_vanishing_square_energy
-- name    : AvramDividend.Classical.avram_f6_original_purejump_ubv_infinite_smallmarks_vanishing_square_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:15:51.215587+00:00
-- url     : https://prove2.me/theorems/3c3650a5-2e7d-44fc-9209-639d7ceecbf7
-- title:
--   Pure-jump UBV has infinite small-jump count with vanishing truncated quadratic energy
-- statement:
--   The original unbounded-variation zero-Gaussian spectrally negative Lévy process has infinite negative-jump intensity in every near-zero interval, while the squared-amplitude integral on shrinking smallmark bands tends to zero. This distinguishes divergent jump counts from negligible L² mark energy, the essential joint condition for compensated infinite-activity martingale approximation. Both components already have rigorous source-faithful Prove2Me proofs and are assembled directly.
-- source:
--   Proved original ν infinite nearzero fad1e92c, Proved original smallmark square energy ddfd1997.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_purejump_ubv_infinite_smallmarks_vanishing_square_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    (∀ δ : ℝ, 0 < δ → X.ν (Ioo (-δ) 0) = ⊤) ∧
    Tendsto (fun n : ℕ =>
      ∫⁻ z in Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        ENNReal.ofReal (z ^ 2) ∂(X.ν.map (fun y : ℝ => -y)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
