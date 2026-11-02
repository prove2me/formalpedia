-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_source_X_integrable_upto_one
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_source_X_integrable_upto_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:49:09.672488+00:00
-- url     : https://prove2.me/theorems/1ed8c860-7066-4f12-aa8a-6f625f35f7f4
-- title:
--   Standing BV Lévy source process has integrable state at every time up to one
-- statement:
--   For the exact original bounded-variation spectrally negative Lévy source satisfying its canonical Standing assumption, the one-time random variable X_t is Bochner integrable at every 0≤t≤1. By the Proved source physical drift residual theorem, R_t=tX.drift-X_t is integrable; the deterministic drift is also integrable under X.isProbability. Thus X_t=tX.drift-R_t is Integrable by subtraction and elementary algebra. No law-based process replacement or additional hypothesis is used. This is necessary for interpreting arbitrary globally Lipschitz C1 transition payoffs at small time.
-- source:
--   Private remote compiler-verified 24-line proof candidates/work_on/AvramDividend_04c_actual_source_X_integrable_upto_one_probe.lean, not yet proof submitted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_source_X_integrable_upto_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (t : ℝ≥0) (ht : t ≤ 1) :
    Integrable (X.X t) P := by sorry
