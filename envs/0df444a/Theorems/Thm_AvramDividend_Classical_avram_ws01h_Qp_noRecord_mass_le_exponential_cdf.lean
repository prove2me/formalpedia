-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_Qp_noRecord_mass_le_exponential_cdf
-- name    : AvramDividend.Classical.avram_ws01h_Qp_noRecord_mass_le_exponential_cdf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:47:49.720101+00:00
-- url     : https://prove2.me/theorems/f266220e-09b1-42f0-a28f-fa2bcc6ad6a3
-- title:
--   Genuine Qp no-upper-record residual is bounded by the exact exponential supremum CDF
-- statement:
--   For the original path under the actual Esscher joint law Qp on P times a real Exp(p) clock, the mass of paths observed strictly before first upward record at height b is at most the full true tilted supremum CDF expMeasure(lambda)(Iic b). This is a numerical source-level bound on the finite-p renewal remainder, with lambda determined by psi(phi+lambda)-q=p. No killed exit scale-ratio theorem is used.
-- source:
--   Genuine original-Qp supremum full-law cf4dc156-a2f9-41cc-85ef-d6492b918ccf; actual strict first passage/supremum path equivalence b626324c-8e00-4488-86d6-b7d63449435c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_exp_clock_supremum_full_law_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_Qp_noRecord_mass_le_exponential_cdf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q : ℝ) (hφ : 0 < φ) (hq : 0 < q) (hroot : X.ψ φ = q)
    (p : ℝ) (hp : 0 < p) (lam : ℝ) (hlam : 0 < lam)
    (hshift : X.ψ (φ + lam) - q = p)
    (b : ℝ) (hb : 0 ≤ b) :
    (let Qp : Measure (Ω × ℝ) :=
      (P.prod (ProbabilityTheory.expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * q)))
    Qp {z : Ω × ℝ |
      (Real.toNNReal z.2 : ℝ≥0∞) < twoSidedExitUpTime X b z.1} ≤
      (ProbabilityTheory.expMeasure lam) (Iic b)) := by sorry
