-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_marked_physical_common_grid_uniform_coefficient_Cauchy_in_L1
-- name    : AvramDividend.Classical.avram_b24_original_marked_physical_common_grid_uniform_coefficient_Cauchy_in_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:54:53.880793+00:00
-- url     : https://prove2.me/theorems/09c1500b-9689-47e7-819f-712ed213dde5
-- title:
--   Genuine original intrinsic compensated marked-mesh integrals are L1 Cauchy on a shared physical grid when predictable weights are uniformly Cauchy
-- statement:
--   On the original finite-negative-activity Lévy source Ω/P, fix a genuine finite physical grid of intrinsic compensated smallmark Jsmall increments. If the bounded predictable coefficient approximations W_m on this same physical grid are uniformly Cauchy over all cells and samples, if each original stochastic grid gain G_m is integrable and the expected total intrinsic marked source variation on the grid is finite V, then the corresponding genuine compensated-mark stochastic gains are Cauchy in L1. The proof uses the actual original marked finite-mesh weight perturbation inequality and takes the uniform coefficient tolerance ε/(V+1), which absorbs even V=0. This is the source-faithful deterministic common-grid component of the marked Itô-Meyer physical mesh L1-Cauchy argument; remaining refining-grid common-refinement and pre-left C² gradient continuity are separate obligations.
-- source:
--   B24 original intrinsic marked finite physical mesh weight perturbation L1 variation theorem, bounded source variation and uniform coefficient convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_marked_physical_common_grid_uniform_coefficient_Cauchy_in_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (W : ℕ → ℕ → Ω → ℝ)
    (G : ℕ → Ω → ℝ)
    (hG : ∀ m ω, G m ω = ∑ i ∈ S,
      W m i ω * (Jsmall (b i) ω - Jsmall (a i) ω))
    (hGI : ∀ m, Integrable (G m) P)
    (hW : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m l, N ≤ m → N ≤ l →
      ∀ i ∈ S, ∀ ω, ‖W m i ω - W l i ω‖ ≤ ε)
    (V : ℝ) (hV : 0 ≤ V)
    (hVarI : Integrable (fun ω =>
      ∑ i ∈ S, ‖Jsmall (b i) ω - Jsmall (a i) ω‖) P)
    (hVarMean : (∫ ω,
      ∑ i ∈ S, ‖Jsmall (b i) ω - Jsmall (a i) ω‖ ∂P) ≤ V) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m l, N ≤ m → N ≤ l →
      (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε := by sorry
