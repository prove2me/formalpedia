-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ripple_original_finitecap_true_stopped_ito_cash_integrable_L1_witness
-- name    : AvramDividend.Classical.avram_ripple_original_finitecap_true_stopped_ito_cash_integrable_L1_witness
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T18:46:39.471837+00:00
-- url     : https://prove2.me/theorems/c46fb312-6783-42ef-af7c-7c3354df8335
-- title:
--   Original finite-cap true stopped Itô–Stieltjes discounted cash source with a jointly integrable L1 limit of physical Brownian gradient and Hessian chaos
-- statement:
--   For the original (not hypothetical) zero-jump unbounded-variation Lévy surplus with a genuine admissible left-continuous dividend control D, original stopped positive reserve floor, caplinear finite cap and original HJB derivative conditions, fix the original bounded random stopped clock rho and its original uniform physical-time masked Brownian gradient-plus-Hessian chaos M_m, actual strict Iio dividendMeasure cash plus discounted prepayment terminal F, and genuine cap-strip occupation Occ. Prove existence of an integrable stopped stochastic-integral witness N with (i) the original stopped discounted Ito-Tanaka-Stieltjes pathwise source inequality on the original positive-clock event, bounded by N plus the explicitly displayed caplinear upper-strip and drift-occupation charges; and (ii) L1 convergence of the exact original physical mesh M_m to N on that positive-clock event. This is the remaining genuinely analytic obstacle to the exact original finite-cap physical positive-part cash L1 source, after the already proved actual Stieltjes cash ledgers, ruin prepayment limits, source integrability and Brownian Hessian cross error estimates. A proof may combine the true original Brownian stochastic integral from Ripple / LevyStochCalc with the actual original clipped physical mesh and dividend Stieltjes accounting. It cannot assume the target source inequality or synthetic L1 premise.
-- source:
--   Existing Proved original strict/allclock Stieltjes ledger a9c657c3 and 13bb448f; actual random-clock prepayment limits bbe7e6a0 and 5a481561; true original Brownian stopped martingale e171e5e8 and discounted 4259127b; source 0ef5d778; Proved general original signed L1 transfer 26f92458, original B Hessian cross 12404271, source integrability 3101fc3d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_ripple_original_finitecap_true_stopped_ito_cash_integrable_L1_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
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
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω),
    ∀ (j : ℕ),
      let M : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η =>
          x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η =>
          X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ≤ b then deriv w (Y i η) else 1)
          else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ≤ b then iteratedDeriv 2 w (Y i η) else 0)
          else 0
        (Finset.range (m + 1)).sum (fun i =>
          G i ω * Z i ω + H i ω *
            (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let F : Ω → ℝ := fun ω =>
          if ρ ω = 0 then w x else
            Real.exp (-(q * (ρ ω : ℝ))) *
              w (riskProcess X x D (ρ ω) ω) +
            (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * z)))
              ∂(dividendMeasure D ω)).toReal
      let Occ : Ω → ℝ := fun ω =>
          ∫ t in Ioo (0 : ℝ) (n : ℝ),
            if t < (ρ ω : ℝ) ∧
                b < riskProcess X x D (Real.toNNReal t) ω
            then (1 : ℝ) else 0 ∂volume
      let A : Set Ω := {ω : Ω | 0 < ρ ω}
      ∃ N : Ω → ℝ,
        Integrable N P ∧
        (∀ᵐ ω ∂(P.restrict A),
          F ω - w x ≤
            N ω + ((w C.toReal - w b) - (C.toReal - b)) +
              max X.c 0 * Occ ω) ∧
        Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
          atTop (nhds (0 : ℝ)) := by sorry
