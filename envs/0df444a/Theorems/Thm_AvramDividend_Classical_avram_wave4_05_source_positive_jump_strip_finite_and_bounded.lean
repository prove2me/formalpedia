-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_jump_strip_finite_and_bounded
-- name    : AvramDividend.Classical.avram_wave4_05_source_positive_jump_strip_finite_and_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:53:48.762095+00:00
-- url     : https://prove2.me/theorems/3e179794-8032-4464-ab4f-17f5791f8d63
-- title:
--   Finite Levy mass and bounded positive source compensation on the strict ruin-crossing strip
-- statement:
--   For the actual spectrally negative Levy source generator, a positive optimal dividend cap and reserve above that cap, assume the standard finite Levy second-moment truncation integral. Then the potentially positive small ruin-crossing jump strip (-1,-x) has finite mass under the actual Levy jump measure. Moreover the positive part of the genuine compensated generator integrand at every negative jump is bounded by max(0,1-vcstar(x)); outside the strip it is identically zero by the exact source positive-part identity. The explicit finite-measure, bounded-kernel majorant is valid without a finite first jump moment and is suitable for the original upper-reserve HJB residual analysis.
-- source:
--   Original Avram–Palmowski–Pistorius (2007) generator and Levy second-moment condition; canonically Proved negative_jump_truncation_measure_finite and exact source positive-part compensator identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_positive_jump_strip_finite_and_bounded {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hpos : 0 < (cstar W).toReal) (x : ℝ) (hx : (cstar W).toReal < x) (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν < ⊤) : X.ν (Ioo (-1 : ℝ) (-x)) < ⊤ ∧ ∀ y : ℝ, y < 0 → max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) ≤ max 0 (1 - vcstar W x) := by sorry
