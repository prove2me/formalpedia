-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_overshoot_integral_le_band_mass
-- name    : AvramDividend.Classical.avram_wave4_05_source_ruin_overshoot_integral_le_band_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:21:04.8126+00:00
-- url     : https://prove2.me/theorems/2b534f57-f383-4696-8098-65ebfd71cf2b
-- title:
--   Strict-ruin compensated overshoot integral is bounded by its finite source Levy mass times its uniform defect
-- statement:
--   For any source spectrally negative Levy jump measure with the original finite Levy second-moment integral and any positive reserve x, the compensated overshoot-defect integral over the strict ruin-crossing small-jump strip (-1,-x) is bounded above by the finite real Levy mass of the strip multiplied by max(0,1-vcstar(x)). The result uses the accepted exact source Bochner-integrable overshoot indicator, finite measure away from zero, and set-integral monotonicity. It requires no Levy first moment and gives an explicit quantitative finite-jump-intensity estimate usable in the original upper-reserve HJB inequality.
-- source:
--   Original source Levy measure truncation assumption, accepted negative-jump truncation finiteness and source ruin overshoot integrability, pinned Mathlib Bochner set integral inequalities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_ruin_overshoot_integral_le_band_mass {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (W : ℝ → ℝ) (x : ℝ) (hx : 0 < x) (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν < ⊤) : (∫ y in Ioo (-1 : ℝ) (-x), max 0 (-vcstar W x - y) ∂X.ν) ≤ (X.ν).real (Ioo (-1 : ℝ) (-x)) * max 0 (1 - vcstar W x) := by sorry
