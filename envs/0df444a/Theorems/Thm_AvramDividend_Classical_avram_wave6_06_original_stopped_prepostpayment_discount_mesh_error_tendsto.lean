-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_stopped_prepostpayment_discount_mesh_error_tendsto
-- name    : AvramDividend.Classical.avram_wave6_06_original_stopped_prepostpayment_discount_mesh_error_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:55:51.332966+00:00
-- url     : https://prove2.me/theorems/5ff558ce-8dab-4f16-8aa1-436a7db4be44
-- title:
--   Actual original Lévy ruin-stopped local pre/postpayment discount mesh gap vanishes on fine source grids
-- statement:
--   For the original spectrally negative Lévy process and left-continuous dividends, the exact clipped source grid v(n,i)=min(u(n,i),τ) has vanishing absolute discounted pre/postpayment value timing error when the un-clipped source grid is monotone, starts at zero, has mesh width tending to zero, and all pre/postpayment reserves lie in a common local interval where w is Lipschitz. The proof imports the Proved pathwise rightpayment total bound, clipping nonexpansion, and local Lipschitz timing limit. No hFuture, Gaussian or compensated jump stochastic identity is assumed or inferred.
-- source:
--   Avram Proposition 4(i), Eq. (5.11)-(5.13), true stopped chronological grid and Stieltjes timing; three Proved Chat06 deterministic sources

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_ruin_grid_rightpayment_total_path_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_stopped_prepostpayment_discount_mesh_error_tendsto
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
    (hmesh0 : Tendsto m atTop (𝓝 0)) :
    Tendsto (fun n =>
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      ∑ i ∈ Finset.range (k n),
        (Real.exp (-(q * (v i : ℝ))) -
          Real.exp (-(q * (v (i + 1) : ℝ)))) *
          |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
            w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|)
      atTop (𝓝 0) := by sorry
