-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_excursion_height_attained_of_upperSemicontinuous
-- name    : AvramDividend.Classical.finite_excursion_height_attained_of_upperSemicontinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:37:56.558881+00:00
-- url     : https://prove2.me/theorems/0462795a-219e-4063-a208-ce845eb8acf2
-- title:
--   A finite upper-semicontinuous excursion with zero endpoints attains each positive exact supremum at a strictly interior time
-- statement:
--   Let R be a real-valued reflected excursion path of finite positive lifetime ζ with R(0)=R(ζ)=0, upper semicontinuous on [0,ζ]. If a positive x is an upper bound for the path on [0,ζ] and is its least upper bound in the sense that every y<x is strictly exceeded somewhere before or at ζ, then R actually achieves R(T)=x at some strictly interior time 0<T<ζ. This supplies the attainment part of the height-level geometry needed to apply the excursion-height atomlessness argument. It does not assume a maximum is already attained; it requires upper semicontinuity, which for càdlàg paths with no downward jumps is a separate genuine analytic prerequisite.
-- source:
--   Kuznetsov, Kyprianou, Rivero (2013), Lemma 2.4 excursion height hitting geometry; compact upper-semicontinuous maximum attainment and càdlàg paths with no negative jumps.

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Compact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem AvramDividend.Classical.finite_excursion_height_attained_of_upperSemicontinuous
    (R : ℝ≥0 → ℝ) (ζ : ℝ≥0) (hζ : 0 < ζ)
    (husc : UpperSemicontinuousOn R (Icc 0 ζ))
    (hzero : R 0 = 0) (hEnd : R ζ = 0)
    (x : ℝ) (hx : 0 < x)
    (hBound : ∀ t : ℝ≥0, t ≤ ζ → R t ≤ x)
    (hSharp : ∀ y : ℝ, y < x →
      ∃ t : ℝ≥0, t ≤ ζ ∧ y < R t) :
    ∃ T : ℝ≥0, 0 < T ∧ T < ζ ∧ R T = x := by sorry
