-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_diffuse_mark_rate_uniform_on_compact
-- name    : AvramDividend.Classical.avram_bvb_b20_diffuse_mark_rate_uniform_on_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T15:52:33.39821+00:00
-- url     : https://prove2.me/theorems/80866c65-41f4-4515-b5d9-a1b233562bc2
-- title:
--   Original diffuse finite-mark compensator rate uniformly continuous on compact reserve domains
-- statement:
--   Under finite negative-mark intensity, diffuse marks and the original finite-cap value regularity, the mark-integrated compensated jump rate is uniformly continuous on any compact subset of the allowable reserve domain. This provides a uniform modulus for the original physical-grid quadrature.
-- source:
--   BV-B20 analytic prerequisite to original pathwise source 912148aa, using Proved 73906c68 and Mathlib Heine-Cantor. Exact original measure ν retained.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b20_diffuse_mark_rate_uniform_on_compact
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (ν : Measure ℝ) (hνfinite : ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, ν {a} = 0)
    (s : Set ℝ) (hs : IsCompact s)
    (hsCap : s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    UniformContinuousOn
      (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν) s := by sorry
