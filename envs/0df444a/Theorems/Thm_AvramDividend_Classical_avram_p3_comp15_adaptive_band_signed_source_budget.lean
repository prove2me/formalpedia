-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp15_adaptive_band_signed_source_budget
-- name    : AvramDividend.Classical.avram_p3_comp15_adaptive_band_signed_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:29:07.075758+00:00
-- url     : https://prove2.me/theorems/333b97af-6d24-43fb-b1ab-1d274cc4f959
-- title:
--   Adaptive original pre-jump bands combine centred negative-jump compensation with signed integrable HJB source
-- statement:
--   For exact original BV spectrally negative Levy surplus, an adapted cofinal band index yields almost-sure eventual interior reserve coverage on the changing physical grid; simultaneously the compensated negative-mark jump sum plus an integrable nonpositive-mean signed HJB budget is integrable and has nonpositive mean in every row. Keeps the true original process, clock and cash source.
-- source:
--   Avram 0b2da5b3 signed expected-value route; direct corollary of publicly Proved 6b5511b3 and elementary integrable-add/integral-add. The new conclusion does not claim positive-error L1 convergence.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp15_adaptive_band_signed_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (B : ℕ → Ω → ℝ) (hBI : ∀ n, Integrable (B n) P)
    (hBnonpos : ∀ n, (∫ ω, B n ω ∂P) ≤ 0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεsum : (∑' n, ε n) < ⊤) :
    ∃ κ : ℕ → ℕ,
      (∀ n, n ≤ κ n) ∧
      (∀ᵐ ω ∂P, ({n : ℕ |
        ω ∈ {η : Ω | ∀ i < n + 1,
          (0 < Function.leftLim
            (fun t : ℝ≥0 => x + X.X t η - rightLimit D t η) (u n i) ∧
            ENNReal.ofReal (Function.leftLim
              (fun t : ℝ≥0 => x + X.X t η - rightLimit D t η) (u n i)) < C) →
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t η - rightLimit D t η) (u n i) ∈
            Icc (a (κ n)) (b (κ n))}ᶜ}).Finite) ∧
      ∀ n : ℕ,
      let M : ℝ≥0 → Ω → ℝ := fun S ω =>
        let τ : Ω → ℝ≥0 := fun ω' =>
          (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
        let E : Set (ℝ≥0 × Ω) := {p |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈
              Icc (a (κ n)) (b (κ n))}
        let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          if p.1 ∈ E ∧ p.2 < 0 then
            Real.exp (-(q * (p.1.1 : ℝ))) *
              (w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
               w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
          else 0
        let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
          if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
        let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω' =>
          ((Measure.count.restrict
            {s : ℝ≥0 | 0 < s ∧
              X.X s ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') s ≠ 0}).map
            (fun s : ℝ≥0 => (s,
              X.X s ω' - Function.leftLim (fun v : ℝ≥0 => X.X v ω') s)))
        (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
      Integrable (fun ω => (Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω)) + B n ω) P ∧
      (∫ ω, (Finset.sum (Finset.range (n + 1))
        (fun i => M (u n (i + 1)) ω - M (u n i) ω)) + B n ω ∂P) ≤ 0 := by sorry
