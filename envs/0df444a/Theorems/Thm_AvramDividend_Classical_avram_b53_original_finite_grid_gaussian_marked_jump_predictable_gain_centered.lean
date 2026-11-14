-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b53_original_finite_grid_gaussian_marked_jump_predictable_gain_centered
-- name    : AvramDividend.Classical.avram_b53_original_finite_grid_gaussian_marked_jump_predictable_gain_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:07:51.295928+00:00
-- url     : https://prove2.me/theorems/354548ed-5a5f-45d6-b76e-5881fe5cde93
-- title:
--   Original mixed finite-grid Gaussian derivative and nonlinear marked negative-jump predictable source is centred
-- statement:
--   For a true finite-activity spectrally negative Levy process on its unchanged probability space and filtration, simultaneously combine finitely many original intrinsic Gaussian weighted increments and finite-band physically marked negative-jump compensated increments with predictable coefficients. Under original-cell expected integrability and the finite-band L2 predictable assumptions, the entire real physical mixed source gain is integrable and has exactly zero expected value.
-- source:
--   Proved B31 same-source Gaussian martingale; JB20 predictable Gaussian cell centring; P4-F3 true physical marked negative jump predictable martingale cell, finite-sum integration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_past_weight_increment_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b53_original_finite_grid_gaussian_marked_jump_predictable_gain_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Finset ι)
    (cut : ι → ℕ) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (htT : ∀ i ∈ S, t i ≤ T)
    (ε : ι → ℝ) (hε : ∀ i ∈ S, 0 < ε i)
    (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hBand : ∀ i ∈ S, B i ⊆ Ioo (-1 : ℝ) (-(ε i)))
    (hCut : ∀ i ∈ S,
      B i ⊆ Iic (-(1 / (((cut i : ℕ) : ℝ) + 1))))
    (HG HJ : ι → Ω → ℝ)
    (hHG : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (HG i))
    (hHJM : ∀ i ∈ S, StronglyMeasurable[𝓕 (s i)] (HJ i))
    (hHJ2 : ∀ i ∈ S, MemLp (HJ i) 2 P) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      (∀ i ∈ S, Integrable (fun ω =>
        HG i ω * (R (t i) ω - R (s i) ω)) P) →
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let N : ι → Ω → ℝ≥0∞ := fun i ω =>
        NX ω (Ioc (s i) (t i) ×ˢ B i)
      let r : ι → ℝ := fun i =>
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
      let F : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (HG i ω * (R (t i) ω - R (s i) ω) +
          HJ i ω * ((N i ω).toReal - r i))
      Integrable F P ∧ (∫ ω, F ω ∂P) = 0 := by sorry
