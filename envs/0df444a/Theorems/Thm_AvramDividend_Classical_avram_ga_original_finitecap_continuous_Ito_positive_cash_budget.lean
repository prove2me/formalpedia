-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_continuous_Ito_positive_cash_budget
-- name    : AvramDividend.Classical.avram_ga_original_finitecap_continuous_Ito_positive_cash_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T16:37:16.240793+00:00
-- url     : https://prove2.me/theorems/b6ae3a09-0d22-40b4-a1ea-1e3847291e9b
-- title:
--   Original finitecap continuous stopped Ito/Tanaka strict cash comparison
-- statement:
--   Continuous-time stopped dividend cash/HJB inequality, for every L1 limiting centred physical grid Z. It must handle the finite-cap downward localtime kink, upper-strip occupation, strict Iio cash and future-dependent fullcell mask through a boundary correction. No unsupported fixed-grid pathwise claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_finitecap_continuous_Ito_positive_cash_budget
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
      let Err : ℕ → Ω → ℝ := fun m ω =>
        (F ω - w x) - M m ω -
          (((w C.toReal - w b) - (C.toReal - b)) +
            max X.c 0 * Occ ω)
      let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (Finset.range m).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω then
          Real.exp (-(q * (s : ℝ))) *
            (if x + X.X s ω - rightLimit D s ω ≤ b
             then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
             else 0) / 2 * (R ^ 2 - Z ^ 2)
        else 0)
∀ Z : Ω → ℝ,
  (∀ m, Integrable (fun ω => |Z ω - M m ω|) (P.restrict A)) →
  Tendsto (fun m => ∫ ω in A, |Z ω - M m ω| ∂P)
    atTop (nhds (0 : ℝ)) →
  (∀ m, (∫ ω in A, max (Err m ω - B m ω) 0 ∂P) ≤
    (∫ ω in A, |Z ω - M m ω| ∂P) +
    (∫ ω, |B m ω| ∂P)) := by sorry
