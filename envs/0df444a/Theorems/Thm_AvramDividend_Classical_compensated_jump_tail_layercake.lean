-- Prove2me | Theorems.Thm_AvramDividend_Classical_compensated_jump_tail_layercake
-- name    : AvramDividend.Classical.compensated_jump_tail_layercake
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:41:58.599709+00:00
-- url     : https://prove2.me/theorems/d2e5ae3b-64c6-4606-b60f-0bdf50cecefe
-- title:
--   Compensated Lévy jump exponent to positive-tail Tonelli identity
-- statement:
--   For any measure of nonnegative jump magnitudes and positive Laplace parameter θ, the nonnegative integral of the compensated jump kernel accumulated from 0 to magnitude z equals the nonnegative integral of the positive jump-tail measure weighted by 1-exp(-θ t). This exact compensated kernel avoids infinity-minus-infinity in infinite-variation Lévy measures, and is a deterministic source obligation in deriving the true original ψ(θ)/θ tail formula.
-- source:
--   Exact Lévy–Khintchine compensation and pinned Mathlib MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul; original target 2fa29eaf-a835-47c5-ad9a-99fe6573547b.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.compensated_jump_tail_layercake
    (μ : Measure ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ z : ℝ≥0,
       ENNReal.ofReal
         (∫ t in (0 : ℝ)..(z : ℝ), (1 - Real.exp (-θ * t))) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ),
        μ {z : ℝ≥0 | t < (z : ℝ)} *
          ENNReal.ofReal (1 - Real.exp (-θ * t)) := by sorry
