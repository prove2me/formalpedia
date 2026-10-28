-- Prove2me | Theorems.Thm_AvramDividend_Classical_first_superlevel_hit_of_upperSemicontinuous
-- name    : AvramDividend.Classical.first_superlevel_hit_of_upperSemicontinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:47:47.584869+00:00
-- url     : https://prove2.me/theorems/783d3753-8828-453c-b82f-e754f8ed9f6d
-- title:
--   A positive level reached by an upper-semicontinuous excursion has a strictly interior earliest superlevel entrance time
-- statement:
--   Let R be an upper-semicontinuous nonnegative-time real-valued path on [0,ζ], starting at R_0=0. For any positive level x reached by R strictly before ζ, the superlevel set {t in [0,ζ]:R_t≥x} is nonempty and compact, so its infimum T belongs to that set. This T is strictly positive, lies strictly before ζ, reaches level x or higher, and precedes every other time in [0,ζ] reaching level x. Unlike the mere existence of an interior maximiser, this constructs the canonical earliest superlevel entrance needed for an excursion first-hit stopping time. It does not assert the measurable stopping-time property.
-- source:
--   Mathlib UpperSemicontinuousOn.isCompact_inter_preimage_Ici and IsCompact.sInf_mem; Kuznetsov-Kyprianou-Rivero (2013) excursion level-hitting argument.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Bornology.Real
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Basic

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem AvramDividend.Classical.first_superlevel_hit_of_upperSemicontinuous
    (R : ℝ≥0 → ℝ) (ζ : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 ζ))
    (hzero : R 0 = 0) (hx : 0 < x)
    (hHit : ∃ t : ℝ≥0, t < ζ ∧ x ≤ R t) :
    ∃ T : ℝ≥0,
      T = sInf (Icc (0 : ℝ≥0) ζ ∩ R ⁻¹' Ici x) ∧
      0 < T ∧ T < ζ ∧ x ≤ R T ∧
      ∀ s : ℝ≥0, s ≤ ζ → x ≤ R s → T ≤ s := by sorry
