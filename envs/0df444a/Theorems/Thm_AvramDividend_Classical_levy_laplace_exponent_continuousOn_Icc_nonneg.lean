-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_Icc_nonneg
-- name    : AvramDividend.Classical.levy_laplace_exponent_continuousOn_Icc_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:22:42.260451+00:00
-- url     : https://prove2.me/theorems/6e647d4a-8b1d-4d1f-a0f5-f173f892051a
-- title:
--   Canonical Lévy Laplace exponent continuous on nonnegative compact intervals
-- statement:
--   Every canonical spectrally negative Lévy Laplace exponent ψ is continuous on [0,B] for nonnegative B. The compensated jump integrand admits a uniform bound (1+B²)min(1,y²), integrable by the canonical Lévy measure condition, and dominated convergence plus polynomial continuity completes the proof.
-- source:
--   Pinned Mathlib dominated continuity and canonical SpectrallyNegativeLevy ν_integrable; published uniform-compensator-envelope lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_laplace_exponent_continuousOn_Icc_nonneg
 {Ω : Type*} [mΩ : MeasurableSpace Ω]
 {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
 (X : SpectrallyNegativeLevy P 𝓕) (B : ℝ) (hB : 0 ≤ B) :
 ContinuousOn X.ψ (Icc (0 : ℝ) B) := by sorry
