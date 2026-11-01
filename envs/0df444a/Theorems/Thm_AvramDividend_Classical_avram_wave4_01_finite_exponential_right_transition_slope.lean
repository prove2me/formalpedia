-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_exponential_right_transition_slope
-- name    : AvramDividend.Classical.avram_wave4_01_finite_exponential_right_transition_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:14:34.525083+00:00
-- url     : https://prove2.me/theorems/b4702d3a-59c4-49ff-bcc5-f4c70fc1a4a5
-- title:
--   Actual Levy transition right-time derivative on finite exponential combinations
-- statement:
--   For arbitrary finite real linear combinations of nonnegative-rate exponential payoffs, the derivative at zero of the actual original-process Levy transition expectation is the corresponding sum of the individual canonical Levy generators. This is a finite-dimensional right-semigroup generator-domain fact established by exponential integrability, exact integral linearity, finite-sum continuity and the already Proved single-exponential right-generator theorem. It does not assert full generator identity of the sum, the unresolved general Ito formula, or stopped Dynkin calculus.
-- source:
--   Proved levy_transition_exponential_right_generator (20c8d029), pinned Mathlib tendsto_finset_sum and finite Bochner integral additivity; Avram–Palmowski–Pistorius (2007) Section 5.

import Mathlib.Topology.Algebra.Monoid
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_right_generator

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_01_finite_exponential_right_transition_slope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ)
    (hrate : ∀ i ∈ s, 0 ≤ rate i) (x : ℝ) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, ∑ i ∈ s, coeff i *
            Real.exp (rate i * (x + X.X (Real.toNNReal h) ω)) ∂P) -
          ∑ i ∈ s, coeff i * Real.exp (rate i * x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (∑ i ∈ s, coeff i *
        X.generator (fun z : ℝ => Real.exp (rate i * z)) x)) := by sorry
