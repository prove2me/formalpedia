-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finitecap_fullmark_gaussian_bounded_grid_initial_centered
-- name    : AvramDividend.Classical.avram_freshD_original_finitecap_fullmark_gaussian_bounded_grid_initial_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:46:48.957123+00:00
-- url     : https://prove2.me/theorems/d6b37ee9-d26c-4977-9419-38aa1434019e
-- title:
--   Original fullmark compensated source jointly centred with every bounded predictable Gaussian grid
-- statement:
--   In the finite-activity, finite-cap original spectrally negative Lévy process, the physical fullnegative marked-jump compensated source at a bounded stopping time is integrable and has zero expectation over all initial-filtration events. Jointly choose the intrinsic continuous Gaussian source R as an almost-sure limit of the original truncated residual; then for every finite grid, adapted bounded predictable weights and the same stopping time, the corresponding stopped Gaussian step integral is integrable and has zero expectation on every initial-filtration event. This directly supplies the fullmark J and arbitrary bounded predictable Gaussian G centredness witnesses required in the finite-cap branch of the original mixed Gaussian and jump positive-excess theorem. The remaining challenge is a physical stopped Ito-Meyer positive-error estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_finitecap_fullmark_gaussian_bounded_grid_initial_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hFiniteCap : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t,
            X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    let J : Ω → ℝ := fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
            atTop (𝓝 (R t ω))) ∧
      Integrable J P ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, J ω ∂P) = 0) ∧
      ∀ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
        (WG : ℕ → Ω → ℝ)
        (hab : ∀ i ∈ S, a i ≤ b i)
        (hWG : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i))
        (L : ℝ) (hL : 0 ≤ L)
        (hWGbound : ∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ L),
      let G : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)
      Integrable G P ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, G ω ∂P) = 0) := by sorry
