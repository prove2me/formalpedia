-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_masked_capped_grid_integral_convergence
-- name    : AvramDividend.Classical.avram_ws01b_actual_masked_capped_grid_integral_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:48:09.577829+00:00
-- url     : https://prove2.me/theorems/67a550ca-dea6-4c40-91af-2a4930d68466
-- title:
--   Actual original Lévy masked capped-grid uniform-integrability transfer without separate history measurability
-- statement:
--   For actual spectrally negative Lévy bounded first-crossing grids, integrability of each full-history killed q-scale reward and its nonnegativity imply a uniform squared-moment bound inherited from the genuine unmasked stopped-grid law. Almost-sure convergence of those rewards then implies convergence of their expectations, with no independent measurability assumption on the moving random history events or limit.
-- source:
--   Accepted original-Lévy stopped-grid L² theorem, pinned Mathlib Integrable.mono, pointwise indicator-square domination, accepted nonnegative uniform-second-moment convergence and a.e measurability from integrable approximants.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_grid_l2_unconditional
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_actual_masked_capped_grid_integral_convergence
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (clock : ℕ → ℕ → ℝ≥0) (hc : ∀ n, Monotone (clock n))
    (hc0 : ∀ n, clock n 0 = 0)
    (H : ℕ → Filtration ℕ mΩ) (hH : ∀ n k, H n k = 𝓕 (clock n k))
    (lower upper : ℝ) (m : ℕ → ℕ) (K : ℕ → Ω → ℕ)
    (hK : ∀ n ω, K n ω = hittingBtwn
      (fun k ξ => max (X.X (clock n k) ξ - upper)
        (lower - X.X (clock n k) ξ)) (Set.Ioi (0 : ℝ)) 0 (m n) ω)
    (N : ℝ≥0) (hNm : ∀ n, clock n (m n) ≤ N)
    (S : ℕ → Set Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n ω, Y n ω = (S n).indicator
      (fun η => Real.exp (-(q * (clock n (K n η) : ℝ))) *
        W (x + X.X (clock n (K n η)) η)) ω)
    (hYi : ∀ n, Integrable (Y n) P)
    (hY0 : ∀ n ω, 0 ≤ Y n ω)
    (Z : Ω → ℝ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (𝓝 (∫ ω, Z ω ∂P)) := by sorry
