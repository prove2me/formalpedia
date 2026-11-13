-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_original_Borel_mark_simple_quantization
-- name    : AvramDividend.Classical.avram_a20_bounded_original_Borel_mark_simple_quantization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T20:49:38.585827+00:00
-- url     : https://prove2.me/theorems/b11524be-a837-4cb4-b1f4-828793bc1cff
-- title:
--   Any bounded original Borel real jump mark has uniformly bounded finite-valued measurable simple approximants converging pointwise on the mark set
-- statement:
--   Given any measurable real mark function g on the actual negative Lévy jump-mark space, a Borel subset S and the bound |g(z)|≤1 on S, there exists a sequence of real SimpleFunc measurable mark functions f_k with absolute value ≤1 everywhere and f_k(z)→g(z) for every z∈S. Define the source mark field by the Borel indicator S.indicator g and apply Mathlib StronglyMeasurable.approxBounded with c=1. The pinned revision proves uniform boundedness and pointwise convergence whenever the indicator field norm is ≤1. The result supplies the quantised finite-range original Borel mark weights needed to extend the already Proved finite disjoint marked-simple Poisson count raw moments to arbitrary bounded marks without assuming a Poisson law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_bounded_original_Borel_mark_simple_quantization
    (g : ℝ → ℝ) (S : Set ℝ)
    (hg : Measurable g) (hS : MeasurableSet S)
    (hBound : ∀ z ∈ S, ‖g z‖ ≤ 1) :
    ∃ f : ℕ → SimpleFunc ℝ ℝ,
      (∀ k z, ‖f k z‖ ≤ 1) ∧
      (∀ z ∈ S, Tendsto (fun k => f k z) atTop (𝓝 (g z))) := by sorry
