-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_stopped_compact_C1_nonlinear_downward_residual_envelope
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_stopped_compact_C1_nonlinear_downward_residual_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:03:42.64078+00:00
-- url     : https://prove2.me/theorems/24173b36-cac5-406e-a08a-bd43c367bfa2
-- title:
--   Actual BV source stopped nonlinear residual loss under only a cell-local compact C1 derivative bound
-- statement:
--   On one probability-one event for the actual original spectrally negative BV Lévy source, the true intrinsic negative left-jump series defines a nondecreasing downward residual R. For every stopped monotone source grid, increasing verification w, and compact interval containing both prepayment reserve and its R-decremented value on every cell, differentiability plus a bounded ordinary derivative only on that compact interval suffices to bound the total weighted nonlinear residual loss by (A*M) times the stopped original source residual variation. This removes the global one-sided Lipschitz hypothesis of the earlier generic source envelope without assuming the controlled Ito-Meyer formula or stochastic integral limits.
-- source:
--   Chat04-A source-only bridge; parent original source exact intrinsic residual decomposition Proved 09869e16-9a95-47e7-b1cd-83739a17b285, stopped nonlinear source envelope Proved 397f2842-72b3-4ce9-80fb-b02c9ec6993f. Distinct stronger cell-local C1 theorem replacing global Lipschitz hypothesis with compact original stopped reserve cell membership, exact derivative control and the pinned Mathlib Convex.norm_image_sub_le_of_norm_deriv_le mean-value inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Cell-local C1 original BV source downward residual variation bound, with the genuine intrinsic source negative left jumps. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_stopped_compact_C1_nonlinear_downward_residual_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw : Monotone w) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (l r M : ℝ) (hlr : l ≤ r) (hM : 0 ≤ M)
        (hdiff : ∀ z ∈ Icc l r, DifferentiableAt ℝ w z)
        (hderiv : ∀ z ∈ Icc l r, |deriv w z| ≤ M)
        (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hcell : ∀ i < n,
          riskProcess X x D (u i) ω ∈ Icc l r ∧
          riskProcess X x D (u i) ω -
            (R (u (i + 1)) - R (u i)) ∈ Icc l r)
        (a : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A)
        (ha : ∀ i, 0 ≤ a i ∧ a i ≤ A),
        0 ≤ (Finset.range n).sum (fun i =>
          a i * (w (riskProcess X x D (u i) ω) -
            w (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))))) ∧
        (Finset.range n).sum (fun i =>
          a i * (w (riskProcess X x D (u i) ω) -
            w (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))))) ≤
          (A * M) * (R (τ ω) - R (u 0)) := by sorry
