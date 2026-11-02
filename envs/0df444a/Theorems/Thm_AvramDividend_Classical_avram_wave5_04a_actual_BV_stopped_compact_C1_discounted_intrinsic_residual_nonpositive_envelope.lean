-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_stopped_compact_C1_discounted_intrinsic_residual_nonpositive_envelope
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_BV_stopped_compact_C1_discounted_intrinsic_residual_nonpositive_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:36:24.301114+00:00
-- url     : https://prove2.me/theorems/cc2db57f-d1d4-4204-a33f-f1ffeffe9664
-- title:
--   Actual original BV compact C1 stopped discounted residual correction is nonpositive and uniformly bounded
-- statement:
--   On a single probability-one event of the actual bounded-variation spectrally negative Levy source, the exact intrinsic original negative left-jump residual R is nondecreasing. For any increasing verification function C1 on the positive-cap interior and any closed interior compact reserve cell, there is a deterministic finite derivative ceiling M. On every stopped monotone source grid with both ends of each residual update in that cell, the discounted nonlinear residual loss is nonnegative and at most M times original residual variation, for every nonnegative discount rate q. The corresponding source contribution is nonpositive; there is no assumed global Lipschitz property or controlled Ito-Meyer formula.
-- source:
--   Chat04-A discounted actual BV source-only application of new canonical Proved deterministic compact C1 stopped residual envelope 633c3d3f-1903-470a-9d31-876b7cdc16fd. Uses elementary 0≤exp(-q*u_i)≤1 for q≥0 and u_i≥0. Strictly more local than old global one-sided Lipschitz discounted envelope, while retaining original intrinsic left jumps and right dividend chronology.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_stopped_C1_compact_deterministic_derivative_ceiling_envelope

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Actual BV source compact C1 residual loss with nonnegative stopped discount weights. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_BV_stopped_compact_C1_discounted_intrinsic_residual_nonpositive_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw : Monotone w)
    (cap l r : ℝ) (hlr : l < r)
    (hsub : Icc l r ⊆ Ioo 0 cap)
    (hC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (q : ℝ) (hq : 0 ≤ q)
        (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hcell : ∀ i < n,
          riskProcess X x D (u i) ω ∈ Icc l r ∧
          riskProcess X x D (u i) ω -
            (R (u (i + 1)) - R (u i)) ∈ Icc l r),
        0 ≤ (Finset.range n).sum (fun i =>
          Real.exp (-q * (u i : ℝ)) *
            (w (riskProcess X x D (u i) ω) -
              w (riskProcess X x D (u i) ω -
                (R (u (i + 1)) - R (u i))))) ∧
        (Finset.range n).sum (fun i =>
          Real.exp (-q * (u i : ℝ)) *
            (w (riskProcess X x D (u i) ω) -
              w (riskProcess X x D (u i) ω -
                (R (u (i + 1)) - R (u i))))) ≤
          M * (R (τ ω) - R (u 0)) := by sorry
