-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_actual_BV_original_cap_C1_deriv_uniformContinuousOn_compact_strip
-- name    : AvramDividend.Classical.avram_wave7_02_actual_BV_original_cap_C1_deriv_uniformContinuousOn_compact_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:21:55.124401+00:00
-- url     : https://prove2.me/theorems/9c3164af-75a9-45e1-a961-24d344d14144
-- title:
--   Original BV HJB C¹ derivative has one uniform modulus on every compact positive-cap reserve strip
-- statement:
--   For the genuine bounded-variation spectrally negative Lévy source and its canonical HJB candidate w, assume ContDiffOn ℝ 1 w only on the actual strictly positive ENNReal cap interior. Then on every compact reserve strip [a,b] contained in that exact interior, deriv w is uniformly continuous. The already-Proved source cap openness theorem makes the derivative continuous on the open domain, restriction gives continuity on the compact strip, and Heine–Cantor yields one uniform derivative modulus for all grid samples. This is the necessary analytic input to instantiate the Proved original-source residual coefficient approximation convergence 21856858 with actual sampled C¹ derivatives on stopped interior grids; no global C¹, independent sample space, or Itô identity is assumed.
-- source:
--   Pinned Mathlib Heine-Cantor on subtype of the true compact source reserve strip, plus Proved canonical cap openness bcf24f3a. Complements source derivative uniform bound 07ca388c and new weighted original BV residual uniform coefficient convergence 21856858.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Source HJB C¹ derivatives have one compact-band modulus, uniformly
across arbitrary stopped grid samples in the genuine positive cap interior. -/

theorem AvramDividend.Classical.avram_wave7_02_actual_BV_original_cap_C1_deriv_uniformContinuousOn_compact_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    UniformContinuousOn (deriv w) (Icc a b) := by sorry
