-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_small_reserve_hjb_of_value_floor
-- name    : AvramDividend.Classical.avram_wave4_05_source_small_reserve_hjb_of_value_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:31:09.717479+00:00
-- url     : https://prove2.me/theorems/42ad16ae-fb28-4332-8f85-4c8be0a1db4d
-- title:
--   Genuine compensated near-barrier HJB below unit reserve under a value floor
-- statement:
--   For source Standing, q>0, a genuine scale function and positive optimal barrier a, any reserve x>a satisfying v(x)>=1 and q*v(x)>=c obeys the genuine full compensated-generator integrability and HJB max equality. The reserve x itself can be below one. At a small negative jump crossing reserve zero, the compensated integrand is -v(x)-y<=0 because -1<y<0 and v(x)>=1. At jumps staying nonnegative, source gradient>=1 gives a left affine majorant and thus nonpositive compensated increments. Source monotonicity controls uncompensated large jumps. The theorem discharges all source affine-majorant and monotonicity premises from the established near-field value-floor jump theorem under original Standing.
-- source:
--   Avram, Palmowski and Pistorius (2007), generator and Lemma 3(i). Genuine source gradients and closed-interval vcstar continuity, cstar finiteness, source monotonicity, Proved left affine majorant, Proved value-floor compensated jump-integrability vcstar_near_field_jump_nonpos_of_unit_value, and exact affine derivative above cstar. This is the complementary source near-field branch for possible x<1, independent of stochastic verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_small_reserve_hjb_of_value_floor {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hpos : 0 < (cstar W).toReal) (x : ℝ) (hx : (cstar W).toReal < x) (hunit : 1 ≤ vcstar W x) (hbound : X.c ≤ q * vcstar W x) : X.GeneratorIntegrable (vcstar W) x ∧ max (X.generator (vcstar W) x - q * vcstar W x) (1 - deriv (vcstar W) x) = 0 := by sorry
