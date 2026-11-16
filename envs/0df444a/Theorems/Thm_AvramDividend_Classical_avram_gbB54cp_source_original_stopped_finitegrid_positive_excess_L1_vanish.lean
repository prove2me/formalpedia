-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_source_original_stopped_finitegrid_positive_excess_L1_vanish
-- name    : AvramDividend.Classical.avram_gbB54cp_source_original_stopped_finitegrid_positive_excess_L1_vanish
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:58:17.072256+00:00
-- url     : https://prove2.me/theorems/561915bd-f233-4775-b341-d00fd0881f47
-- title:
--   Original stopped finite-cap Gaussian physical-mesh positive cash residual L1 tends to zero
-- statement:
--   For the genuine original bounded stopped Gaussian Lévy strategy with strict prepayment dividend cash, actual centered physical-grid M_m and upper cap occupation correction, the integral of max((F-w(x))-corner-max(c,0)*Occ-M_m,0) on the given initial event tends to zero. This source-equivalent one-sided error is independent of the L1 limit N and is precisely the stochastic Ito-Tanaka/Stieltjes mesh theorem needed for the B54cp positive-clock cash budget through the already Proved eventwise L1 transfer. No Brownian companion, smooth fullcell absolute-Taylor assumption, or spurious upper kink local-time cancellation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB54cp_source_original_stopped_finitegrid_positive_excess_L1_vanish
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
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
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
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1)
          else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0)
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
      Tendsto (fun m =>
        ∫ ω in A,
          max ((F ω - w x) -
            (((w C.toReal - w b) - (C.toReal - b)) +
              max X.c 0 * Occ ω) - M m ω) 0 ∂P)
        atTop (nhds (0 : ℝ)) := by sorry
