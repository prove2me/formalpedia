-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_ruinclip_marked_source_HJB_negative_generator
-- name    : AvramDividend.Classical.avram_twoagentA_original_allnu_ruinclip_marked_source_HJB_negative_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T11:18:13.167549+00:00
-- url     : https://prove2.me/theorems/c31d24cf-bdca-4b2d-b352-8527e24798e2
-- title:
--   Original full-Lévy-activity ruin-clipped jump martingale and physical HJB nonpositive generator/tail certificate
-- statement:
--   Under unrestricted Gaussian variance and negative Lévy activity, the actual original ruin-clipped nonlinear Taylor/finite annular linear compensated jump source is jointly centered and integrable, while on the SAME original process the compact predictable true-clock HJB generator drift is integrable and nonpositive with vanishing original compensator tails. This is a genuine physical source ledger component, leaving same-space Gaussian and small linear compensated cut-off L2 convergence and the complete signed dividend pathwise ledger open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_ruinclip_fullnu_joint_Taylor_finite_annuli_centered
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_true_clock_HJB_nonpositive_with_negative_generator_tails
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_twoagentA_original_allnu_ruinclip_marked_source_HJB_negative_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (Cband u v δ : ℝ)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband))
    (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (huv : u + δ < v) (hv : v < Cband)
    (S : Finset ℕ) (η : ℕ → ℝ)
    (hη : ∀ i, 0 < η i ∧ η i < 1)
    (hw_gen : ∀ y : ℝ, 0 < y → y < Cband →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (a : ℝ≥0 × Ω → ℝ)
    (ham : Measurable[𝓕.rightCont.predictable] a)
    (ha : ∀ p, 0 ≤ a p ∧ a p ≤ 1) :
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
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      ρ p.1 * (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable R μ ∧
      (∫ p, R p ∂μ) ≤ 0 ∧
      Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
        ‖a p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂μ)
        atTop (𝓝 0) ∧
      Integrable (fun ω => J τ ω + ∑ i ∈ S, L i ω) P ∧
      (∫ ω, J τ ω + ∑ i ∈ S, L i ω ∂P) = 0 := by sorry
