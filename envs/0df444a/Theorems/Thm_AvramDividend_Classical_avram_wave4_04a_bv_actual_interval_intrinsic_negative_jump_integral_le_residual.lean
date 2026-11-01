-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_intrinsic_negative_jump_integral_le_residual
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_interval_intrinsic_negative_jump_integral_le_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:08:59.473826+00:00
-- url     : https://prove2.me/theorems/cbc2e9a0-6ab9-4203-bcc0-c4a96882d592
-- title:
--   Genuine original BV Lévy intrinsic jump measure has interval-local finite negative-mark integral bounded by source residual loss
-- statement:
--   On the same probability-one event of the actual original bounded-variation Lévy process, and for all s≤t, the intrinsic source jump counting measure N_X(ω) has nonnegative jump mark magnitude integral ∫_(s,t] (-z)^+ N_X(ω;du,dz) dominated by the genuine residual increment ((t*d−X_t)-(s*d−X_s)). This is the true BV uncompensated source jump mass on a localized time window, suitable for stopping-time and reserve-dependent subsequent control kernels; it is not a predictable Campbell expectation, compensator, or pure-jump drift equality. Derives via exact original-path lintegral-to-jump-sum identity and new accepted interval Stieltjes jump total-variation budget.
-- source:
--   Canonical Proved e4542c93-c64b-453a-b582-e5ec26265dfc source intrinsic Nω lintegral sum; new original interval source Stieltjes jump variation target 0ebd2a44-06bf-4a28-a9db-4e70c0ac84c8 (canonically Proved, accepted candidate 19704); Mathlib ENNReal.measurable_ofReal and tsum_congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_interval_intrinsic_negative_jump_integral_le_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      (∫⁻ p,
        (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≤
      ENNReal.ofReal
        (((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω)) := by sorry
