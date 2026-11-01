-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_of_ruin_band_mass_criterion
-- name    : AvramDividend.Classical.avram_wave4_05_source_hjb_of_ruin_band_mass_criterion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:24:19.899132+00:00
-- url     : https://prove2.me/theorems/e4cfad8a-ea85-48ae-8f04-c640ecc1d8a1
-- title:
--   True source upper HJB from a finite ruin-band Levy intensity bound
-- statement:
--   For a source spectrally negative Levy process and positive dividend barrier a with x>a, the genuine compensated generator is in its domain and the entire source HJB maximum vanishes when the source drift plus the finite real Levy mass of the strict small ruin-crossing band (-1,-x) times max(0,1-vcstar(x)) is at most q*vcstar(x). The standard Levy second-moment condition is explicit. This combines the exact source positive-part kernel identity, integrable overshoot and a quantitative finite-band intensity bound, without assuming a first Levy moment or extra Gaussian/variation hypotheses.
-- source:
--   Avram Palmowski Pistorius 2007 compensated generator, accepted source HJB from strict ruin-overshoot integral bound and source overshoot integral finite-mass bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_hjb_of_ruin_band_mass_criterion {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hpos : 0 < (cstar W).toReal) (x : ℝ) (hx : (cstar W).toReal < x) (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν < ⊤) (hmass : X.c + (X.ν).real (Ioo (-1 : ℝ) (-x)) * max 0 (1 - vcstar W x) ≤ q * vcstar W x) : X.GeneratorIntegrable (vcstar W) x ∧ max (X.generator (vcstar W) x - q * vcstar W x) (1 - deriv (vcstar W) x) = 0 := by sorry
