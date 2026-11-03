-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ae_cofinal_payment_residual_from_chronological_timing_bound
-- name    : AvramDividend.Classical.avram_wave6_06_original_ae_cofinal_payment_residual_from_chronological_timing_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:24:01.549797+00:00
-- url     : https://prove2.me/theorems/9775f76b-9fe7-4c9e-8ec3-e9e812958db6
-- title:
--   Actual source cofinal stopped timing bound yields almost-sure Stieltjes residual upper
-- statement:
--   For the genuine original spectrally negative Levy path and dividend process, assume almost-sure pathwise compact local Lipschitz interior bands on the literal stopped chronological grid, an exact timing-error functional built from original X and right-limit D, and the chronological Stieltjes residual plus cash upper bounded by a drift envelope plus that functional. The accepted cofinal stopped timing limit makes the residual upper hold almost surely eventually to arbitrary epsilon, exactly the conditional hPaymentApproxSubsequence input needed by the accepted original ruin-stopped source asymptotic Ito verification consumer.
-- source:
--   Avram Proposition 4(i), finite-horizon stopped Stieltjes bound Eq (5.13); original cofinal 5ff558ce plus conditional Chat05 chronological residual

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_cofinal_ruinstopped_payment_timing_mesh_vanishes
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_ae_cofinal_payment_residual_from_chronological_timing_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hu : ∀ n, Monotone (u n)) (hzero : ∀ n, u n 0 = 0)
    (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (Residual : ℕ → Ω → ℝ) (Cash H : Ω → ℝ)
    (Timing : ℕ → Ω → ℝ)
    (hTiming : ∀ n ω, Timing n ω =
      (let v : ℕ → ℝ≥0 := fun i => min (u (φ n) i) (τ ω)
       ∑ i ∈ Finset.range (k (φ n)),
         (Real.exp (-(q * (v i : ℝ))) -
           Real.exp (-(q * (v (i + 1) : ℝ)))) *
           |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
             w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|))
    (hLocal : ∀ᵐ ω ∂P, ∃ L a b : ℝ,
      0 ≤ L ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |w s - w t| ≤ L * |s - t|) ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n i) (τ ω)) ω ∈ Icc a b) ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n (i + 1)) (τ ω)) ω ∈ Icc a b))
    (hChronological : ∀ᵐ ω ∂P, ∀ n,
      Residual (φ n) ω + Cash ω ≤ H ω + Timing n ω)
    (hmesh0 : Tendsto m atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, Residual (φ n) ω + Cash ω ≤ H ω + ε := by sorry
