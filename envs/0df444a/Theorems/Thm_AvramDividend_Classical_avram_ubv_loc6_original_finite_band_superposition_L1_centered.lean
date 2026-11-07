-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_finite_band_superposition_L1_centered
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_finite_band_superposition_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:08:47.356275+00:00
-- url     : https://prove2.me/theorems/0fb4b55e-e6a7-4a6d-a943-547059793cf1
-- title:
--   Finite superposition of original stopped compensated negative jump bands is L1 centred
-- statement:
--   For a finite family of actual negative-jump bands on the original Lévy process, stopped at the same right-continuous clock below the natural ruin horizon, the sum of their finite-grid compensated increments is integrable and has zero expectation, provided each predictable coefficient is L2. This is the finite-superposition step needed before a small-band Cauchy limit.
-- source:
--   Source-exact finite superposition of the already Proved original arbitrary compact negative-grid L1 centring theorem 10525210; retains all compensator, cutoff, time-grid and original stopping assumptions. Neither an infinite sum nor a uniform-integrability conclusion is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_original_finite_band_superposition_L1_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (Cap : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x Cap D)
    (n : ℕ) (T : ℝ≥0) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (S : Finset ι)
    (C : ι → ℕ → Set ℝ)
    (hC : ∀ j i, MeasurableSet (C j i))
    (hBand : ∀ j i, C j i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ j i, C j i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (N : ι → ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ j i, N j i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C j i))
    (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ j i, StronglyMeasurable[𝓕.rightCont (grid i)] (H j i))
    (hHL2 : ∀ j i, MemLp (H j i) 2 P)
    (τ σ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσle : ∀ ω, σ ω ≤ τ ω)
    (k : ℕ) :
    Integrable (fun ω => ∑ j ∈ S, ∑ i ∈ Finset.range k,
      (if (σ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
       then (0 : ℝ) else H j i ω) *
      ((N j i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C j i)).toReal)) P ∧
    (∫ ω, (∑ j ∈ S, ∑ i ∈ Finset.range k,
      (if (σ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
       then (0 : ℝ) else H j i ω) *
      ((N j i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C j i)).toReal)) ∂P) = 0 := by sorry
