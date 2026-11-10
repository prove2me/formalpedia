-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_before_first_negative_jump_source_increments_zero
-- name    : AvramDividend.Classical.avram_bv_zero13_original_before_first_negative_jump_source_increments_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:30:33.635364+00:00
-- url     : https://prove2.me/theorems/a2c33db6-507a-4f83-9d50-e249e7b3ce4b
-- title:
--   No actual physical Levy jump strictly before first negative source jump
-- statement:
--   For every original spectrally negative Levy source sample path, any positive time strictly before the infimum of actual strictly negative physical jump times has zero source jump increment. Exact source pathwise spectral negativity says any nonzero positive-time mark must be negative, which would contradict the assumed strict precedence by the infimum inequality. This is the missing direct hypothesis-discharge for strict-open pre-first-jump zero-reserve Stieltjes cash f62dae07; it uses no auxiliary process or a.e. approximation and needs no BV/finite-rate assumptions itself.
-- source:
--   Root-connected BV-ZERO13 original strict pre-negative-jump zero-reserve Stieltjes cash requires no source jumps on the open interval. Proved physical first-clock 48fcb9f3 and strict-open cash f62dae07 are its downstream consumers.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_before_first_negative_jump_source_increments_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hBefore : (t : WithTop ℝ≥0) <
      (⨅ u : ℝ≥0,
        if 0 < u ∧
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
        then (u : WithTop ℝ≥0) else ⊤)) :
    X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t = 0 := by sorry
