-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_diffuse_finite_mark_rate_uniform_bounded_on_compact
-- name    : AvramDividend.Classical.avram_bvb_b20_diffuse_finite_mark_rate_uniform_bounded_on_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:27:29.15709+00:00
-- url     : https://prove2.me/theorems/39a3699a-d1ad-478c-958c-3d249a0c6837
-- title:
--   Finite original diffuse-mark compensation rate admits a uniform compact bound
-- statement:
--   The original finite-intensity diffuse negative-mark integral has a uniform absolute bound on every nonempty compact subset of admissible reserve values. This supplies the finite domination required by the one-sided upper-Fatou uniform-grid comparison.
-- source:
--   Boundedness component of original phys95/d022 one-sided marked quadrature using compact extreme-value theorem and Proved B19 continuity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b20_diffuse_finite_mark_rate_uniform_bounded_on_compact
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (ν : Measure ℝ) (hνfinite : ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, ν {a} = 0)
    (s : Set ℝ) (hs : IsCompact s) (hsNonempty : s.Nonempty)
    (hsCap : s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ b ∈ s, |∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν| ≤ M := by sorry
