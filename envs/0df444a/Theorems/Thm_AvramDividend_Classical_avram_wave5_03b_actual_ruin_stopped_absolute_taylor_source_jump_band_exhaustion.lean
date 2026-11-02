-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_absolute_taylor_source_jump_band_exhaustion
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_absolute_taylor_source_jump_band_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:58:45.140482+00:00
-- url     : https://prove2.me/theorems/2a743fed-2f08-4c76-95de-a5080b6ec3db
-- title:
--   Actual stopped nonlinear source jump absolute integral is the supremum of its increasing negative jump-band integrals
-- statement:
--   For the literal original SpectrallyNegativeLevy X and adapted dividend strategy D, the inclusive ruin-stopped C2 Taylor remainder at the true prepayment reserve yields a nonnegative absolute jump reward. For every sample ω, time interval (s,t], and increasing Borel mark bands B_n exhausting all negative marks, the supremum of true intrinsic source marked jump integrals over B_n equals the integral over all negative marks. The result is an exact pathwise monotone-convergence identity for the actual source, without a Finset enumeration or an independent Poisson copy. It does not assert finiteness or compensated martingale convergence.
-- source:
--   Proved actual original-source jointly predictable C2 stopped Taylor kernel 0e0663b1; pinned Mathlib monotone convergence lintegral_iSup; source jump-series identification 039daa2b and rightCont source lift e58a099d. No compensated source intensity assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_randomly_stopped_predictable_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_absolute_taylor_source_jump_band_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (B : ℕ → Set ℝ) (hBmeas : ∀ n, MeasurableSet (B n))
    (hBmono : Monotone B)
    (hBcover : ∀ z : ℝ, z < 0 ↔ ∃ n : ℕ, z ∈ B n) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let J : ℝ≥0 → Ω → ℝ := fun q ω =>
      X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {q : ℝ≥0 | 0 < q ∧ J q ω ≠ 0}).map
        (fun q : ℝ≥0 => (q, J q ω)))
    ∀ (s t : ℝ≥0) (ω : Ω),
      (⨆ n : ℕ,
        (∫⁻ p : ℝ≥0 × ℝ,
          (if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B n then
            ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω)) =
      (∫⁻ p : ℝ≥0 × ℝ,
        (if s < p.1 ∧ p.1 ≤ t ∧ p.2 < 0 then
          ENNReal.ofReal (|HS ((p.1,ω),p.2)|) else 0) ∂NX ω) := by sorry
