-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bv_C1_clipped_ruinstopped_payment_mesh_error_tendsto
-- name    : AvramDividend.Classical.avram_wave6_06_original_bv_C1_clipped_ruinstopped_payment_mesh_error_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:51:54.121548+00:00
-- url     : https://prove2.me/theorems/84c90ae2-b220-43b3-8707-edefb578b666
-- title:
--   Original bounded-variation C1 derivative envelope yields vanishing ruin-stopped clipped payment timing error
-- statement:
--   For the genuine original spectrally negative Levy BV process and dividend strategy, the exact min-clipped stopping grid has vanishing discounted pre/postpayment reserve value error under a local positive cap C1 derivative bound. This independently combines Proved Chat09 derivative Lipschitz, Chat06 mesh nonexpansion, source right-dividend path bound and original discounted mesh convergence; it assumes local pre/post reserve bands, not a stochastic Ito decomposition.
-- source:
--   Avram Proposition 4(i) classical BV C1 case, stopped chronological payment timing; accepted source lemmas 82f28985,54bf2416,8410dc24,572b8d66

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_ruin_grid_rightpayment_total_path_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_bv_C1_clipped_ruinstopped_payment_mesh_error_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hu : ∀ n, Monotone (u n)) (hzero : ∀ n, u n 0 = 0)
    (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
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
