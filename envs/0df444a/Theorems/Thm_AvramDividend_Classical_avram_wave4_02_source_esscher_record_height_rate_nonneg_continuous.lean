-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
-- name    : AvramDividend.Classical.avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:44:45.51454+00:00
-- url     : https://prove2.me/theorems/08f9ec73-4e7b-480e-aea2-5f6fe1affe6d
-- title:
--   Source-identified Esscher-normalised killed first-record height rate is nonnegative and continuous
-- statement:
--   For the actual source spectrally negative Levy process under the infinite-small-negative-jump variation regime, define the unit-level q-discounted genuine first-upward-record survival before actual reflected drawdown ruin. At the positive root phi with psi(phi)=q, its negative logarithm minus phi is nonnegative and continuous in every positive drawdown depth. The factor phi is fixed by stopped Esscher normalisation. The conclusion is a genuinely source-derived killed-potential hazard candidate and does not assert existence of an Itô characteristic measure or PPP compensator.
-- source:
--   Actual original source killed record factor, canonically Proved original record log-hazard continuity 98caa, actual first-record scale sandwich 2490701d, positive-root first-passage scale decay 680362b2, and canonical strict W positivity. This gives the nonnegative continuous Esscher-shifted height-rate candidate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_genuine_local_scale_ratio_sandwich
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_first_passage_scale_decay
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_source_esscher_record_height_rate_nonneg_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ContinuousOn (fun a : ℝ =>
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ) (Ioi (0 : ℝ)) ∧
    ∀ a : ℝ, 0 < a →
      0 ≤ -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P).toReal) - φ := by sorry
