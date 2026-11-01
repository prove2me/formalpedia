-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_of_strict_ruin_overshoot_integral_bound
-- name    : AvramDividend.Classical.avram_wave4_05_source_hjb_of_strict_ruin_overshoot_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:19:03.463435+00:00
-- url     : https://prove2.me/theorems/4d92a086-81d0-4ef8-98fc-aa74369c3b58
-- title:
--   Original source HJB reduces to a finite strict-ruin overshoot integral bound above a positive barrier
-- statement:
--   For a source spectrally negative Levy process, q-scale function W, positive optimal cap a and reserve x>a, the full HJB residual vanishes if the source drift plus the integral under the genuine Levy measure of the positive compensated ruin-crossing defect on the strict band (-1,-x) is at most q times vcstar(x). The strict band integral is genuine Bochner integrable under the original Levy second-moment assumption, and the original generator is in its domain. Pointwise the source compensated kernel is bounded above by the band overshoot indicator at every negative jump, while the derivative above the cap is one. This is a fully compensated-source reduction of the upper HJB to a finite-jump-band scalar inequality, without a Levy first moment or extra Gaussian or bounded-variation premise.
-- source:
--   Avram Palmowski Pistorius 2007 original compensated generator and HJB, source generator-above drift-plus-jump identity, accepted exact positive-part jump identity and source overshoot L1 integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_hjb_of_strict_ruin_overshoot_integral_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hpos : 0 < (cstar W).toReal) (x : ℝ) (hx : (cstar W).toReal < x) (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν < ⊤) (hbound : X.c + (∫ y in Iio (0 : ℝ), (Ioo (-1 : ℝ) (-x)).indicator (fun z : ℝ => max 0 (-vcstar W x - z)) y ∂X.ν) ≤ q * vcstar W x) : X.GeneratorIntegrable (vcstar W) x ∧ max (X.generator (vcstar W) x - q * vcstar W x) (1 - deriv (vcstar W) x) = 0 := by sorry
