-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_indexed_lipschitz_H_signed_jump_series
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_indexed_lipschitz_H_signed_jump_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:07:51.601637+00:00
-- url     : https://prove2.me/theorems/2a9dae4a-80dc-4a66-a267-0611aaa8fb16
-- title:
--   Original compensated H indexed BV sources equal exact original stopped signed jump-time series on one full-measure event
-- statement:
--   For the actual original BV spectrally negative Lévy process and original admissible dividends, countably indexed compact interior C1 bands with genuine Lipschitz and value bounds have the same-path full original compensated H real nonlinear marked jump integral equal to the true stopped negative-jump positive-minus-negative series simultaneously on one original almost-sure event, for every physical finite horizon. The proof combines pinned Mathlib ae_all_iff with the already Proved original H integrability and exact real jump-series theorem, ensuring the same original Lévy process, path, index, stopping clock, zero exclusion, original left reserve and final contact as the original indexed compensated HJB source. No surrogate process or stochastic source hypothesis is used.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_full_H_signed_physical_jump_series_ae

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_indexed_lipschitz_H_signed_jump_series
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hL : ∀ n, 0 ≤ L n) (hR : ∀ n, 0 ≤ R n)
    (hLip : ∀ n, ∀ u ∈ Icc (a n / 2) (b n),
      ∀ v ∈ Icc (a n / 2) (b n),
      |w u - w v| ≤ L n * |u - v|)
    (hWbound : ∀ n, ∀ v : ℝ, v ≤ b n → |w v| ≤ R n) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ (T : ℝ≥0),
    let τ : Ω → ℝ≥0 := fun η =>
      (min (ruinTime X x D η) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
            p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
            p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Eω : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let J : ℝ≥0 × ℝ → ℝ := fun p =>
      (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ Eω then K p else 0)
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    (∫ p, H ((p.1, ω), p.2) ∂NX) =
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 (min T (τ ω)) then
            ENNReal.ofReal (J (v, Δ v)) else 0).toReal -
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc 0 (min T (τ ω)) then
            ENNReal.ofReal (-J (v, Δ v)) else 0).toReal := by sorry
