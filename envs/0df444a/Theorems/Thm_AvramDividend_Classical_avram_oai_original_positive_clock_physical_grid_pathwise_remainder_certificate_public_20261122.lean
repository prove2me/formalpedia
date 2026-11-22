-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_positive_clock_physical_grid_pathwise_remainder_certificate_public_20261122
-- name    : AvramDividend.Classical.avram_oai_original_positive_clock_physical_grid_pathwise_remainder_certificate_public_20261122
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T20:44:14.016716+00:00
-- url     : https://prove2.me/theorems/5e94ab55-18c7-4abb-8ea3-73c6196604a4
-- title:
--   Avram original infinite-activity positive-clock stopped physical Itô–Meyer finite simple marked-grid pathwise HJB residual and vanishing expected error certificate
-- statement:
--   This is the EXACT REMAINING NONTRIVIAL PATHWISE STOCHASTIC CALCULUS SOURCE for the mission-connected Open node 6d006466. Under the full original spectrally negative Lévy Gaussian-plus-infinite-jump dividend assumptions and each genuine stopped positive clock σ_k, produce for EVERY approximation level j finitely many deterministic time intervals (s_{j,i},t_{j,i}], locally finite-intensity negative Borel mark cells S_{j,i}, signed real finite-range mark integrands g_{j,i}, bounded predictable pre-time weights H_{j,i} supported on the positive-clock initial event A={σ_k≠0}, and remainder E_j. The ACTUAL intrinsic physically marked-jump compensated signed noise M_j is explicitly defined from those data, with the original stopping-time survival mask 1_{σ_k>s_{j,i}}. Prove each mark set finite intensity despite infinite total activity, each weight right-continuous-past measurable and bounded, every weight zero off A, each E_j integrable on A, the TRUE source stopped HJB pathwise inequality F_k≤w x+M_j+E_j almost surely on A, and ∫_A E_j→0. There are DELIBERATELY NO ASSUMED centring or integrability properties of M_j: these are discharged by the independently REMOTELY PROVED all-activity true physical stopped variable signed simple-mark grid theorem f17bb762 and the original initial-event support. This new Open source theorem isolates the exact Itô–Meyer generator, Gaussian and infinite-jump remainder gap for a mathematically sound SKETCH_ACCEPTED mission-graph reduction of parent 6d006466 → 26bf9d58 → Avram root. It does not claim the original nonlinear Itô identity is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_positive_clock_physical_grid_pathwise_remainder_certificate_public_20261122
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
      ∃ (m : ℕ → ℕ)
        (s t : ℕ → ℕ → ℝ≥0)
        (S : ℕ → ℕ → Set ℝ)
        (g : ℕ → ℕ → SimpleFunc ℝ ℝ)
        (H : ℕ → ℕ → Ω → ℝ)
        (K : ℕ → ℕ → ℝ)
        (E : ℕ → Ω → ℝ),
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
        (∀ j, IntegrableOn (E j) A P) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A),
          F k ω ≤ w x + M j ω + E j ω) ∧
        Tendsto (fun j => ∫ ω in A, E j ω ∂P)
          atTop (𝓝 (0 : ℝ)) := by sorry
