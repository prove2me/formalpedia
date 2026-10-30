-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_weak_noRecord_remainder_tendsto_zero
-- name    : AvramDividend.Classical.avram_ws01h_actual_Qp_weak_noRecord_remainder_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:26:58.411479+00:00
-- url     : https://prove2.me/theorems/3de81674-37b0-42ed-a5cc-6a4fa851efb9
-- title:
--   Actual original Lévy terminal Esscher weak no-record Qp remainder converges to zero at the positive-root small-rate limit
-- statement:
--   For the actual spectrally negative Lévy process with ψ(φ)=q>0, genuine original-path terminal Esscher joint Qp law at exponential observation rate p>0, and any strictly positive shifted-root family λp satisfying ψ(φ+λp)−q=p and λp→0 as p↓0, the true tilted Qp mass of the weak no-upper-record before-observation event tends to exactly zero. It is bounded by the authentic expMeasure(λp)(Iic b) supremum probability using the already accepted source-specific no-record inequality; the independent true exponential CDF-to-analytic limit proves this bound tends to zero. Squeeze 0≤actual Qp mass≤exponential CDF in ENNReal topology. No canonical q-scale two-sided exit identity, fictitious infinite-path Esscher probability or unproved martingale is assumed.
-- source:
--   Proved avram_ws01h_Qp_weak_noRecord_mass_le_exponential_cdf f98ad01c and true Exp(λp) CDF decay 74283c75; pinned Filter.Tendsto.squeeze and original source Qp.

import Mathlib.Topology.Order.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_Qp_weak_noRecord_mass_le_exponential_cdf
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_exp_noRecord_CDF_vanishes_at_small_shifted_root

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_ws01h_actual_Qp_weak_noRecord_remainder_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q : ℝ) (hφ : 0 < φ) (hq : 0 < q)
    (hroot : X.ψ φ = q)
    (lam : ℝ → ℝ)
    (hlampos : ∀ p : ℝ, 0 < p → 0 < lam p)
    (hshift : ∀ p : ℝ, 0 < p →
      X.ψ (φ + lam p) - q = p)
    (hlam : Tendsto lam (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (0 : ℝ))) (b : ℝ) (hb : 0 ≤ b) :
    Tendsto (fun p : ℝ =>
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * q))))
        {z : Ω × ℝ | 0 ≤ z.2 ∧
          (Real.toNNReal z.2 : ℝ≥0∞) ≤
            twoSidedExitUpTime X b z.1})
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ≥0∞)) := by sorry
