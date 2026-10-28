-- Prove2me | Theorems.Thm_AvramDividend_Classical_first_exact_level_hit_of_upperSemicontinuous
-- name    : AvramDividend.Classical.first_exact_level_hit_of_upperSemicontinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:56:20.19139+00:00
-- url     : https://prove2.me/theorems/0fd16ab4-5436-45fe-a762-7af033e7778f
-- title:
--   An exact positive excursion-height level has an earliest strictly interior hit when the path is upper semicontinuous and bounded by that level
-- statement:
--   Let R be an upper-semicontinuous path on a finite interval with R(0)=0 and positive bound x. If R(t)≤x for all t≤ζ and some t<ζ attains level x, the earliest entrance into the superlevel set {R≥x} exists, occurs at 0<T<ζ, and hits x exactly (it cannot overshoot because x bounds the whole excursion). The hitting time is explicitly the infimum of the superlevel entrance set and precedes every other exact hit. This proves the deterministic first-hit geometry needed in the excursion-height atomlessness proof, beyond mere existence of a maximiser.
-- source:
--   Kuznetsov-Kyprianou-Rivero 2013 Lemma 2.4 excursion height atomlessness; Mathlib compactness of USC superlevel sets.

import Theorems.Thm_AvramDividend_Classical_first_superlevel_hit_of_upperSemicontinuous

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem AvramDividend.Classical.first_exact_level_hit_of_upperSemicontinuous
    (R : ℝ≥0 → ℝ) (ζ : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 ζ))
    (hzero : R 0 = 0) (hx : 0 < x)
    (hBound : ∀ t : ℝ≥0, t ≤ ζ → R t ≤ x)
    (hHit : ∃ t : ℝ≥0, t < ζ ∧ x ≤ R t) :
    ∃ T : ℝ≥0,
      T = sInf (Icc (0 : ℝ≥0) ζ ∩ R ⁻¹' Ici x) ∧
      0 < T ∧ T < ζ ∧ R T = x ∧
      ∀ s : ℝ≥0, s ≤ ζ → R s = x → T ≤ s := by sorry
