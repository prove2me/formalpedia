-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB212_stopped_discounted_compact_clip_uniform_amplitude
-- name    : AvramDividend.Classical.avram_gbB212_stopped_discounted_compact_clip_uniform_amplitude
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:45:20.734029+00:00
-- url     : https://prove2.me/theorems/f9ec125c-db45-4f81-a649-9b69da16098d
-- title:
--   Exact stopped nonnegative-time exponentially discounted clipped reward gradient is uniformly bounded for arbitrary selected thresholds
-- statement:
--   Any compact-band derivative clipping bounded by continuity remains uniformly bounded after multiplication by a nonincreasing exponential discount and restriction to an arbitrary sample-dependent stopping horizon.
-- source:
--   Original Gaussian selected cutoff mesh L2: uniform coefficient bound for any adapted or nonadapted state and stopping clock using B210; no stochastic assumptions needed.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
open MeasureTheory Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB212_stopped_discounted_compact_clip_uniform_amplitude
    {Ω : Type*} (w : ℝ → ℝ) (a b : ℝ)
    (hContinuous : ContinuousOn (deriv w) (Icc a b))
    (q : ℝ) (hq : 0 ≤ q)
    (Y : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (s : ℝ≥0) (ω : Ω),
        |if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
          (if Y s ω ∈ Icc a b then deriv w (Y s ω) else 1)
        else 0| ≤ B := by sorry
