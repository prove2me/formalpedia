-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_positive_clock_signed_ito_mesh_with_exact_cash_boundary_20261122
-- name    : AvramDividend.Classical.avram_oai_original_positive_clock_signed_ito_mesh_with_exact_cash_boundary_20261122
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:15:00.441475+00:00
-- url     : https://prove2.me/theorems/9fdcff4b-59b8-4c17-aa69-48aa72082d19
-- title:
--   Original mixed Gaussian and infinite-jump stopped physical Ito mesh with separately explicit full discounted dividend cash boundary
-- statement:
--   The original public stopped physical Ito-Meyer source with exact last-cash L1 error explicitly isolated. All assumptions of parent 5e94ab55 are preserved. For each genuine stopped clock σ_k and each cash mesh index selector r_j, produce actual finite time cells and signed negative ν-finite Borel simple marked physical jump integrals, bounded predictable coefficients supported on A={σ_k≠0}, plus an integrable stochastic residual R_j with ∫_A R_j→0, such that the original discounted post-right-payment terminal plus closed-Iic dividend cash reward F_k≤w x+M_j+R_j+CashErr_j pathwise on A. CashErr_j is exactly qΔ multiplied by original dividendMeasure on (0,σ_k) plus the actual discount integral on (σ_k-Δ,σ_k), with Δ=n/(r_j+1). This remaining open source does NOT assume full/global finite Lévy activity, a synthetic PRM, or a predetermined Gaussian martingale. The cash-error control, including choice of r_j and restricted L1 convergence, is independently discharged by PROVED rootward helpers 9a9388 and cd1d3912 in a real subsequent sketch of parent 5e94ab55; the open child then isolates the nonlinear Gaussian and infinite-jump true physical stopped Ito–Meyer source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_positive_clock_signed_ito_mesh_with_exact_cash_boundary_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ k : ℕ,
      let A : Set Ω := {ω | σ k ω ≠ 0}
      ∀ r : ℕ → ℕ,
      let CashErr : ℕ → Ω → ℝ := fun j ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((r j : ℝ≥0) + 1)
        let u : ℝ≥0 := σ k ω - Δ
        q * (Δ : ℝ) *
          (dividendMeasure D ω (Ioo (0 : ℝ) (σ k ω : ℝ))).toReal +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal

      ∃ (m : ℕ → ℕ)
        (s t : ℕ → ℕ → ℝ≥0)
        (S : ℕ → ℕ → Set ℝ)
        (g : ℕ → ℕ → SimpleFunc ℝ ℝ)
        (H : ℕ → ℕ → Ω → ℝ)
        (K : ℕ → ℕ → ℝ)
        (R : ℕ → Ω → ℝ),
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        let B : ℕ → ℕ → ℝ → Set ℝ := fun j i y =>
          S j i ∩ (g j i) ⁻¹' {y}
        let G : ℕ → ℕ → Ω → ℝ := fun j i ω =>
          ∑ y ∈ (g j i).range, y *
            ((NX ω (Ioc (s j i) (t j i) ×ˢ B j i y)).toReal -
              ((((t j i - s j i : ℝ≥0) : ℝ≥0∞) *
                X.ν (B j i y))).toReal)
        let M : ℕ → Ω → ℝ := fun j ω =>
          ∑ i ∈ Finset.range (m j),
            (if (σ k ω : WithTop ℝ≥0) ≤
                  (s j i : WithTop ℝ≥0)
              then 0 else H j i ω) * G j i ω
        (∀ j, ∀ i ∈ Finset.range (m j), s j i < t j i) ∧
        (∀ j, ∀ i ∈ Finset.range (m j), MeasurableSet (S j i)) ∧
        (∀ j, ∀ i ∈ Finset.range (m j), S j i ⊆ Iio (0 : ℝ)) ∧
        (∀ j, ∀ i ∈ Finset.range (m j), X.ν (S j i) < ⊤) ∧
        (∀ j, ∀ i ∈ Finset.range (m j),
          StronglyMeasurable[𝓕.rightCont (s j i)] (H j i)) ∧
        (∀ j, ∀ i ∈ Finset.range (m j), ∀ ω,
          ‖H j i ω‖ ≤ K j i) ∧
        (∀ j, ∀ i ∈ Finset.range (m j), ∀ ω,
          ω ∉ A → H j i ω = 0) ∧
        (∀ j, IntegrableOn (R j) A P) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A),
          F k ω ≤ w x + M j ω + R j ω + CashErr j ω) ∧
        Tendsto (fun j => ∫ ω in A, R j ω ∂P)
          atTop (𝓝 (0 : ℝ)) := by sorry
