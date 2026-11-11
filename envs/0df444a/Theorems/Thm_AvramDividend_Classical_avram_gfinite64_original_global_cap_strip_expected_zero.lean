-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite64_original_global_cap_strip_expected_zero
-- name    : AvramDividend.Classical.avram_gfinite64_original_global_cap_strip_expected_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:01:49.35762+00:00
-- url     : https://prove2.me/theorems/9168b6b5-5dbd-4b7c-96ea-07d4a39ae974
-- title:
--   Original UBV globally capped process has vanishing expected upper-cap strip time
-- statement:
--   For the original unbounded-variation process on its original probability space, any globally real-capped admissible dividend strategy spends asymptotically zero expected Lebesgue time in the open strip between the increasing fractional caps c (j+1)/(j+2) and the actual cap c, over each finite deterministic horizon. This source-exact clock-free estimate follows from the established strict fixed-time boundary theorem, joint measurability, Fubini and continuity of finite measure from above. It supplies an upper bound for the stopped time-strip occupation appearing in A07 finite-cap Gaussian verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite64_original_global_cap_strip_expected_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (hc : 0 < c)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0), riskProcess X x D s ω ≤ c)
    (n : ℕ) (hn : 0 < n) :
    Tendsto
      (fun j : ℕ => ∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
        if c * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
            riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0 ∂volume ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
