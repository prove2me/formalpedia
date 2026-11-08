-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian13_actual_stopped_bracket_expectation_limit
-- name    : AvramDividend.Classical.avram_ubv_gaussian13_actual_stopped_bracket_expectation_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:38:05.14719+00:00
-- url     : https://prove2.me/theorems/2d12d313-0964-415e-a32a-39c2ee162862
-- title:
--   Original Gaussian stopped bracket expectations converge at bounded physical clocks
-- statement:
--   On Avram's original right-continuous filtration, suppose uniformly bounded stopping times converge almost surely and the actual compact-masked Gaussian bracket has continuous sample paths. Then the expectations of stopped quadratic brackets converge, by a deterministic L¹ envelope from the compact derivative and the genuine bounded stopped-bracket integrability results. All original stopping times, square-energy and filtration are preserved.
-- source:
--   Adapts Fukasawa Chapter11BoundedStoppedExpectation and Chapter10L2DominatedLocalMartingale, using Proved original Gaussian10 predictable-square-energy, terminal L¹ and stopped bracket monotonicity; explicitly isolates continuity of physical time bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_square_energy_integrableOn
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_square_bracket_le_deterministic
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_terminal_bracket_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_bounded_stopped_bracket_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_capped_ruin_bracket_le_horizon

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian13_actual_stopped_bracket_expectation_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (μtime : Measure ℝ≥0) [SFinite μtime] (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤)
    (τ : Ω → ℝ≥0) (τn : ℕ → Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτnstop : ∀ n, IsStoppingTime 𝓕.rightCont
      (fun ω => (τn n ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ T)
    (hτnbound : ∀ n ω, τn n ω ≤ T)
    (hτconv : ∀ᵐ ω ∂P, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    (∀ ω, Continuous (fun r : ℝ≥0 =>
      ∫ z in Ioc (0 : ℝ≥0) r, (G (z, ω)) ^ 2 ∂μtime)) →
    Tendsto (fun n => ∫ ω, (∫ z in Ioc (0 : ℝ≥0) (τn n ω),
      (G (z, ω)) ^ 2 ∂μtime) ∂P) atTop
      (𝓝 (∫ ω, (∫ z in Ioc (0 : ℝ≥0) (τ ω),
        (G (z, ω)) ^ 2 ∂μtime) ∂P)) := by sorry
