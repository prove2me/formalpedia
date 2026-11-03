-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bv_C1_band_derivative_discounted_payment_mesh_limit
-- name    : AvramDividend.Classical.avram_wave6_06_original_bv_C1_band_derivative_discounted_payment_mesh_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:45:23.657957+00:00
-- url     : https://prove2.me/theorems/a6a75ca5-4852-4252-8c94-572c9b98f74b
-- title:
--   Original BV C1 interior derivative bound removes Lipschitz premise from discounted payment mesh convergence
-- statement:
--   For the original spectrally negative Levy process in bounded variation, C1 regularity and a bounded derivative on a positive finite-cap reserve strip imply the exact discounted pre/postpayment mesh timing error tends to zero. The proof composes the Proved Chat09 C1 derivative-to-Lipschitz source lemma with the Proved Chat06 original D payment timing limit. Both reserves must stay in the strip and total pathwise right payments must remain bounded; neither stochastic compensated/Gaussian identity nor a source stopping identity is assumed.
-- source:
--   Avram Proposition 4(i), Equation (5.11)-(5.13), BV C1 source interior and Stieltjes timing; Proved 82f28985 + 54bf2416

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_bv_C1_band_derivative_discounted_payment_mesh_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (k : ℕ → ℕ) (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (hPre : ∀ n i, i < k n →
      x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω ∈ Icc a b)
    (hPost : ∀ n i, i < k n →
      x + X.X (u n (i + 1)) ω - rightLimit D (u n (i + 1)) ω ∈ Icc a b)
    (htotal : ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      rightLimit D (u n (k n)) ω - rightLimit D (u n 0) ω ≤ B)
    (hmesh0 : Tendsto m atTop (𝓝 0)) :
    Tendsto (fun n =>
      ∑ i ∈ Finset.range (k n),
        (Real.exp (-(q * (u n i : ℝ))) -
          Real.exp (-(q * (u n (i + 1) : ℝ)))) *
          |w (x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω) -
            w (x + X.X (u n (i + 1)) ω - rightLimit D (u n (i + 1)) ω)|)
      atTop (𝓝 0) := by sorry
