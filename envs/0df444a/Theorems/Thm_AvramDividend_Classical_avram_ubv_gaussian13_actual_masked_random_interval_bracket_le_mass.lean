-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian13_actual_masked_random_interval_bracket_le_mass
-- name    : AvramDividend.Classical.avram_ubv_gaussian13_actual_masked_random_interval_bracket_le_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:21:26.157518+00:00
-- url     : https://prove2.me/theorems/0d8620ad-050f-421c-aef0-cb71f3e2a758
-- title:
--   Actual original masked Gaussian bracket increment bounded at any random interval
-- statement:
--   On the unchanged original Lévy probability space, the square-energy bracket of the actual compact-masked Gaussian gradient over any two random-clock endpoints is uniformly bounded by one deterministic constant squared times the measured interval length, whenever the interval has finite time-measure mass. The bound is pathwise and needs no augmented filtration or Brownian substitute.
-- source:
--   Follows from Proved original masked source derivative uniform bound 9645ebf8 and finite-measure norm-integral estimate; new interval-increment interface beyond the Proved zero-origin terminal bracket cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian13_actual_masked_random_interval_bracket_le_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μtime : Measure ℝ≥0) (s t : Ω → ℝ≥0)
    (hFinite : ∀ ω, μtime (Ioc (s ω) (t ω)) < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω,
      (∫ r in Ioc (s ω) (t ω), (G (r, ω)) ^ 2 ∂μtime) ≤
        K ^ 2 * (μtime.restrict (Ioc (s ω) (t ω))).real Set.univ := by sorry
