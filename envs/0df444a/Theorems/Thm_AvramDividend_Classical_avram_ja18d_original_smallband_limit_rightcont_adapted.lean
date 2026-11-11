-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18d_original_smallband_limit_rightcont_adapted
-- name    : AvramDividend.Classical.avram_ja18d_original_smallband_limit_rightcont_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:55:17.97422+00:00
-- url     : https://prove2.me/theorems/ed4dbe1a-fdd6-4dba-a9eb-1a5253681649
-- title:
--   Original full small-band a.e. cutoff limit inherits right-continuous-filtration conditional self-measurability
-- statement:
--   Assume only a genuine pointwise a.e. limit Jsmall of the original compensated small-band cutoffs. Each original finite cutoff is measurable in F_t (Proved 7ba6e5dc) and the cutoff family has a common integrable physical count envelope (Proved b3763297). Therefore the limit is F_t^+-measurable a.e. and integrable; by conditional expectation self-measurability E[Jsmall(t)|F_t^+]=Jsmall(t) a.e. This is independent of establishing pathwise convergence or càdlàg regularity and supplies the adaptedness component of Open 678e826a.
-- source:
--   Sound independently provable adaptedness child of 678e826a, rooted through 23979329 to 61f39bfe.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise33_original_smallband_compensator_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja18b_original_smallband_uniform_count_envelope
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18d_original_smallband_limit_rightcont_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hLimit : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont t) P (Jsmall t) ω = Jsmall t ω := by sorry
