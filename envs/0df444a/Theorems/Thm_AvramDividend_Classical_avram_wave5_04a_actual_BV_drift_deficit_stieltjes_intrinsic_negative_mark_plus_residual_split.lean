-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_drift_deficit_stieltjes_intrinsic_negative_mark_plus_residual_split
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_BV_drift_deficit_stieltjes_intrinsic_negative_mark_plus_residual_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:31:05.012029+00:00
-- url     : https://prove2.me/theorems/0f7a35f4-c0f1-41a4-822c-a3ce0501f0ae
-- title:
--   Exact actual BV Stieltjes drift-deficit interval measure equals intrinsic negative marks plus downward residual growth
-- statement:
--   For the actual bounded-variation spectrally negative Levy source on one probability-one event, there is its genuine drift-deficit Stieltjes function F(t)=t*X.drift-X_t and an explicitly defined nondecreasing downward residual R after removing all physical source negative left jumps. Every (s,t] interval of the Stieltjes measure F.measure has real mass exactly equal to the original intrinsic negative-mark counting-measure integral on (s,t] plus R_t-R_s. At each positive singleton {t}, the same F.measure atom is exactly the magnitude of the actual source left jump. This is the required measure-level decomposition, without identifying R as zero or assuming an Ito-Meyer stochastic integral.
-- source:
--   Chat04-A source measure bridge: combine the canonically Proved original drift-deficit Stieltjes singleton atom theorem 0c2826fa-5cd3-4dcb-bef0-9a029879d9b2, true original intrinsic BV mark residual interval theorem 09869e16-9a95-47e7-b1cd-83739a17b285, and pinned Mathlib StieltjesFunction.measure_Ioc to convert F(t)-F(s) to measure mass. The nonnegative residual and marks justify ENNReal.toReal_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_residual_stieltjes_atom_is_source_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Complete original BV drift-deficit Stieltjes interval mass is exactly
the genuine intrinsic negative source mark mass plus monotone residual
growth. The same physical Stieltjes function has precisely the actual
source negative jump at every singleton atom. No Ito--Meyer integration. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_BV_drift_deficit_stieltjes_intrinsic_negative_mark_plus_residual_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ (F : StieltjesFunction ℝ≥0) (R : ℝ≥0 → ℝ),
      (∀ t : ℝ≥0,
        (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      (∀ t : ℝ≥0, 0 < t →
        F.measure {t} =
          ENNReal.ofReal (Function.leftLim
            (fun u : ℝ≥0 => X.X u ω) t - X.X t ω)) ∧
      ∀ (s t : ℝ≥0), s ≤ t →
        (F.measure (Ioc s t)).toReal =
          (∫⁻ p,
            (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal +
          (R t - R s) := by sorry
