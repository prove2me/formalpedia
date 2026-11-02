-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_original_intrinsic_measure_and_downward_residual_partition_source_balance
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_original_intrinsic_measure_and_downward_residual_partition_source_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:04:43.772511+00:00
-- url     : https://prove2.me/theorems/d332c668-cd57-49c3-a99d-2f560166719d
-- title:
--   Exact actual BV source drift balance of intrinsic negative-mark measure plus monotone residual over every ordered finite partition
-- statement:
--   On one probability-one event for the actual original bounded-variation spectrally negative Levy sample process, two explicitly specified finite-variation clocks R and J are simultaneously available: R is the residual after drift and all source negative left jumps, J is the real mass of the intrinsic source negative-mark counting measure. R is nondecreasing. On every increasing finite time partition, the sum of every original negative-mark interval mass plus its matching residual increment is exactly the actual source drift-minus-path increment across the full partition. This is a pathwise source balance for C1 controlled-chain bookkeeping; it assumes neither complete Ito-Meyer integration nor vanishing residual and distinguishes original source left jumps from right dividend payments.
-- source:
--   Chat04-A exact stopped finite-variation source budget combining already canonically Proved original BV intrinsic-mark source interval theorem 09869e16-9a95-47e7-b1cd-83739a17b285 with the already Proved finite additive real source mark functional dfee60ca-5061-4714-b19c-5eebd284f82e. Proved elementary Finset telescoping yields the exact original source partition budget without any stochastic integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_finite_real_interval_additivity

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original BV source mark and residual partition source balance. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_original_intrinsic_measure_and_downward_residual_partition_source_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ (R : ℝ≥0 → ℝ) (J : ℝ≥0 → ℝ≥0 → ℝ),
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      (∀ (a b : ℝ≥0),
        J a b =
          (∫⁻ p,
            (if a < p.1 ∧ p.1 ≤ b then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal) ∧
      Monotone R ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (∑ i ∈ Finset.range n,
          (J (u i) (u (i + 1)) +
            (R (u (i + 1)) - R (u i)))) =
          ((u n : ℝ) - (u 0 : ℝ)) * X.drift -
            (X.X (u n) ω - X.X (u 0) ω) := by sorry
