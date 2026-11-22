-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_finiteactivity_intrinsic_gaussian_smalljump_JL_joint_centered
-- name    : AvramDividend.Classical.avram_twoagentA_original_finiteactivity_intrinsic_gaussian_smalljump_JL_joint_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T11:08:48.931497+00:00
-- url     : https://prove2.me/theorems/cad61fc9-7fab-424a-93f1-0c12adb9693a
-- title:
--   Original physical finite-activity four-component stopped Gaussian, small-mark, Taylor and linear-jump L1 centred certificate
-- statement:
--   At the actual original ruin-clipped stopping time for finite negative Levy activity, the original intrinsic Gaussian and compensated small-band limits exist and combine with the original same-X nonlinear Taylor jump integral and any finite family of annular linear gradient marks to form an integrable zero-mean four-component physical stochastic source. No synthetic centred reward or auxiliary process is introduced. The full unbounded-activity limit, signed dividend ledger and HJB source still require separate proofs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_bounded_clock_continuous_gaussian_smallmark_both_eventwise_centered
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_ruinclip_fullnu_joint_Taylor_finite_annuli_centered
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_twoagentA_original_finiteactivity_intrinsic_gaussian_smalljump_JL_joint_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (Cband u v δ : ℝ)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband))
    (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (huv : u + δ < v) (hv : v < Cband)
    (S : Finset ℕ) (η : ℕ → ℝ)
    (hη : ∀ i, 0 < η i ∧ η i < 1) :
    let T : ℝ≥0 := (n : ℝ≥0)
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
        (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
    let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
      (∫ p, (if p.1 ≤ ρ ω then GW ((p.1, ω), p.2) else 0) ∂(NX ω)) -
      (∫ t, ∫ z,
        (if t ≤ ρ ω then GW ((t, ω), z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    let K : ℕ → Ω → (ℝ≥0 × ℝ) → ℝ := fun i ω p =>
      if p.1 ≤ T ∧ p.2 ∈ Ioo (-1 : ℝ) (-(η i)) then
        Real.exp (-(q * (p.1 : ℝ))) *
          (if Y (p.1, ω) ∈ Icc (u + δ) v then
            deriv w (Y (p.1, ω)) * p.2 else 0) else 0
    let L : ℕ → Ω → ℝ := fun i ω =>
      (∫ p, (if p.1 ≤ τ ω then K i ω p else 0) ∂(NX ω)) -
      (∫ t, ∫ z, (if t ≤ τ ω then K i ω (t,z) else 0)
        ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
    ∃ (G Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (G t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      Integrable (fun ω =>
        (G (τ ω) ω + Jsmall (τ ω) ω) +
          (J τ ω + ∑ i ∈ S, L i ω)) P ∧
      (∫ ω, (G (τ ω) ω + Jsmall (τ ω) ω) +
          (J τ ω + ∑ i ∈ S, L i ω) ∂P) = 0 := by sorry
