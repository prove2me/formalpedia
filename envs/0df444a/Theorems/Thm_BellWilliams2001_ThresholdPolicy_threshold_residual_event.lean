-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_residual_event
-- name    : BellWilliams2001.ThresholdPolicy.threshold_residual_event
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:07:14.222142+00:00
-- url     : https://prove2.me/theorems/6594588c-3cbf-4691-977e-f7cfed71b1af
-- title:
--   A quantitative common event for the initial threshold hit and the residual band
-- statement:
--   For a sufficiently large logarithmic threshold coefficient, the first threshold hit is bounded by D log r and the class 1 residual stays strictly inside Lʳ−1 after the hit on the diffusion horizon, off a measurable event of probability at most C(2+t)/r⁶.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, Theorem 7.2 and the quantitative estimates used in (174)–(176)

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

theorem threshold_residual_event {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∃ D C : ℝ, 0 < D ∧ 0 ≤ C ∧
      ∀ T : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (T n) ∧ M.IsThreshold c n (T n)) →
      ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → ∃ E : Set Ω, MeasurableSet E ∧
      M.P E ≤ ENNReal.ofReal (C*(2+t)/M.r n^6) ∧ ∀ ω ∉ E,
        let τ : ℝ≥0∞ := ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : (M.threshold c n : ℝ) ≤ M.queue n (T n) ω 0 s),
          ENNReal.ofReal s
        τ ≤ ENNReal.ofReal (D*Real.log (M.r n)) ∧
          ∀ s : ℝ, 0 ≤ s → τ ≤ ENNReal.ofReal s → s ≤ M.r n^2*t →
            |M.queue n (T n) ω 0 s - (M.threshold c n : ℝ)| < (M.threshold c n : ℝ)-1 := by sorry

end BellWilliams2001.ThresholdPolicy
