-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_physical_prefix_separate_source
-- name    : AvramDividend.Classical.avram_bv_meas7_original_physical_prefix_separate_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:39:34.946214+00:00
-- url     : https://prove2.me/theorems/d5712b28-bee8-4d03-a03f-fa0a8c295168
-- title:
--   Original BV stopped physical shrinking-prefix jump martingale is L1 centred
-- statement:
--   For each physical mesh index n with delta_n=T/(n+2), establish mathematically that the strict-grid prefix T-delta_n is nonnegative and equals its NNReal truncation. At this exact prefix, on the genuine original ruin-clipped BV X,D process, every admissible indexed compact pre-reserve strip has separately integrable X.nu compensated jump M with expectation zero, and integrable nonpositive-mean HJB drift B. No surrogate laws or independent stochastic assumptions. The source cash/contact-cell inequality and positive-error limit are still needed for 4f605d76.
-- source:
--   Source-exact specialisation of Proved 3221b81c to the same physical index n and the literal real endpoint T-delta_n used by Open 4f605d76; proves the endpoint is nonnegative and returns the original continuous stopped compensated M/B at this exact prefix. Does not assume any stochastic integrability or mean-zero hypothesis; does not assert the missing pathwise cash or mesh-error conclusion.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_indexed_compact_separate_source

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_physical_prefix_separate_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
    (T : ℝ) (hT : 0 < T) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ n : ℕ,
    let δ : ℕ → ℝ := fun k => T / ((k : ℝ) + 2)
    let S : ℝ≥0 := Real.toNNReal (T - δ n)
    ((S : ℝ) = T - δ n) ∧
    (let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
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
    let F : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
         (∫ z in Iio (0 : ℝ),
            w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
            w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
         q * w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1))
      else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let M : Ω → ℝ := fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
    let B : Ω → ℝ := fun ω =>
      ∫ t, F (t, ω)
        ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal)
    (Integrable M P ∧ (∫ ω, M ω ∂P) = 0) ∧
      (Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0)) := by sorry
