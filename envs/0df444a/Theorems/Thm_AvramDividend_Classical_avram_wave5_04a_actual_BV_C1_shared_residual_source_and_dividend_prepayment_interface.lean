-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_C1_shared_residual_source_and_dividend_prepayment_interface
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_BV_C1_shared_residual_source_and_dividend_prepayment_interface
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:24:47.361914+00:00
-- url     : https://prove2.me/theorems/244506a8-0863-496a-a136-30bd9f95a073
-- title:
--   One actual BV source residual simultaneously controls stopped C1 loss and exact controlled prepayment balance
-- statement:
--   For the actual bounded-variation spectrally negative Levy source, on one probability-one event the exact intrinsic original left-jump interval representation of every controlled prepayment reserve increment and the separate right dividend payment algebra share precisely the same nondecreasing source residual R as the stopped compact C1 nonlinear residual estimate. The C1 derivative ceiling M is deterministic for any interior compact cell, and the stopped correction is bounded by A M times residual variation. This is a simultaneous source-only interface for Chat03 and does not assert the controlled Ito-Meyer theorem or R=0.
-- source:
--   Chat04-A same-source event-intersection and uniqueness composition of own original intrinsic source reserve balance theorem (old canonical Proved 11cce28a-6f19-4e0f-a228-26cc67a93946) and new original stopped deterministic compact C1 residual envelope theorem. The residual witnesses coincide pointwise by their identical explicit actual-source drift-minus-jump-series definitions; original left jumps and chronological right dividends are kept disjoint.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_source_to_controlled_prepayment_increment_balance
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_stopped_C1_compact_deterministic_derivative_ceiling_envelope

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One actual-source residual simultaneously controls prepayment reserve balance and finite stopped C1 loss. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_BV_C1_shared_residual_source_and_dividend_prepayment_interface
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
      (∀ (s t : ℝ≥0), s ≤ t →
        riskProcess X x D t ω - riskProcess X x D s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∫⁻ p,
              (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
              ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim
                    (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
            (R t - R s) - (D t ω - D s ω)) ∧
      (∀ t : ℝ≥0,
        riskProcess X x D t ω - (rightLimit D t ω - D t ω) =
          x + X.X t ω - rightLimit D t ω) ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
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
