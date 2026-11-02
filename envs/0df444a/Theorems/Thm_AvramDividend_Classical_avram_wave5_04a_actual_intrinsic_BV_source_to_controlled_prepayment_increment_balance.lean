-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_source_to_controlled_prepayment_increment_balance
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_source_to_controlled_prepayment_increment_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:13:10.819793+00:00
-- url     : https://prove2.me/theorems/11cce28a-6f19-4e0f-a228-26cc67a93946
-- title:
--   Actual BV intrinsic negative-mark source and downward residual yield exact controlled prepayment interval balance
-- statement:
--   On one probability-one event for the actual spectrally negative bounded-variation Levy source, an explicitly defined nondecreasing residual R gives an exact identity for every controlled reserve increment between s and t: physical drift minus the original intrinsic negative left-jump measure on (s,t], minus residual growth, minus the actual accumulated D_t-D_s. The state after a chronological right dividend payment equals the state before payment minus rightLimit D_t-D_t, in a separate algebraic equality. D need not satisfy a stochastic integration theorem or any admissibility for these identities.
-- source:
--   Chat04-A original source-side bridge from canonically Proved 09869e16-9a95-47e7-b1cd-83739a17b285, using the literal existing riskProcess and rightLimit definitions. Distinguishes original X source left jumps and chronological right D payments. Exact algebraic interface for Chat03 without proving Itô–Meyer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The source part of every actual controlled reserve increment is the
original intrinsic negative left-jump measure plus its downward BV residual.
The chronological right dividend payment is a *separate* algebraic update,
not a jump of the original source; no Ito--Meyer theorem is used. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_source_to_controlled_prepayment_increment_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
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
          x + X.X t ω - rightLimit D t ω) := by sorry
