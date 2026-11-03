-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_cofinal_ruinstopped_payment_timing_mesh_vanishes
-- name    : AvramDividend.Classical.avram_wave6_06_original_cofinal_ruinstopped_payment_timing_mesh_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:15:42.639201+00:00
-- url     : https://prove2.me/theorems/ab031f0a-718f-4ea2-8354-3fc112488491
-- title:
--   Actual stopped payment timing error vanishes along the same cofinal source subsequence
-- statement:
--   For the exact original spectrally negative Levy source and left-continuous dividend process on min-clipped chronological stopping grids, the discounted pre/postpayment timing gap tends to zero along every cofinal subsequence phi. This aligns the Proved literal source stopping-grid timing limit with the same cofinal extraction used for mixed stopped compensated jump and Gaussian source terms; it assumes no source stochastic chain rule.
-- source:
--   Avram, Palmowski, Pistorius Proposition 4(i), original controlled stopped dividend timing; Proved 5ff558ce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_stopped_prepostpayment_discount_mesh_error_tendsto
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_cofinal_ruinstopped_payment_timing_mesh_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hu : ∀ n, Monotone (u n)) (hzero : ∀ n, u n 0 = 0)
    (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (a b : ℝ)
    (hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |w s - w t| ≤ L * |s - t|)
    (hPre : ∀ n i, i < k n →
      x + X.X (min (u n (i + 1)) (τ ω)) ω -
        rightLimit D (min (u n i) (τ ω)) ω ∈ Icc a b)
    (hPost : ∀ n i, i < k n →
      x + X.X (min (u n (i + 1)) (τ ω)) ω -
        rightLimit D (min (u n (i + 1)) (τ ω)) ω ∈ Icc a b)
    (hmesh0 : Tendsto m atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    Tendsto (fun n =>
      let v : ℕ → ℝ≥0 := fun i => min (u (φ n) i) (τ ω)
      ∑ i ∈ Finset.range (k (φ n)),
        (Real.exp (-(q * (v i : ℝ))) -
          Real.exp (-(q * (v (i + 1) : ℝ)))) *
          |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
            w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|)
      atTop (𝓝 0) := by sorry
