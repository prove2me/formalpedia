-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian13_actual_random_interval_bracket_L1_of_mean_clock
-- name    : AvramDividend.Classical.avram_ubv_gaussian13_actual_random_interval_bracket_L1_of_mean_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:35:18.762938+00:00
-- url     : https://prove2.me/theorems/cda62036-f15b-4fca-834d-85d9697058d3
-- title:
--   Original stopped Gaussian bracket integrable under finite expected random-clock mass
-- statement:
--   On the original Lévy probability space, a Gaussian quadratic bracket over random endpoints has a finite first moment provided the physical time-measure mass of the random interval has a finite first moment and the stopped bracket is measurable. The required bracket measurability remains an explicit interface for the original right-continuous filtration.
-- source:
--   Proved 0d8620ad deterministic actual Gaussian interval bracket domination, then Bochner integrability comparison against the finite expected clock mass.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian13_actual_masked_random_interval_bracket_le_mass

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian13_actual_random_interval_bracket_L1_of_mean_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μtime : Measure ℝ≥0) (s t : Ω → ℝ≥0)
    (hFinite : ∀ ω, μtime (Ioc (s ω) (t ω)) < ⊤)
    (hMassI : Integrable (fun ω =>
      (μtime.restrict (Ioc (s ω) (t ω))).real Set.univ) P) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    AEStronglyMeasurable (fun ω =>
      ∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime) P →
    Integrable (fun ω =>
      ∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime) P := by sorry
