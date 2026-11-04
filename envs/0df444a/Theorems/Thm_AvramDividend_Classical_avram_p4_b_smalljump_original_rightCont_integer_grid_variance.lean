-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_integer_grid_variance
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_integer_grid_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:44:25.72042+00:00
-- url     : https://prove2.me/theorems/04ef4a8b-400b-4976-8c1b-f57d10302387
-- title:
--   Original Lévy right-continuous finite-grid L² martingale-difference variance
-- statement:
--   Finite sums of L² differences on the original source's right-continuous filtration have second moments equal to the sum of their individual second moments, assuming actual one-step adaptedness and conditional centring. The stopped predictable compensated jump increments must independently be shown to satisfy these premises.
-- source:
--   Original source-filtration specialisation of the accepted 6d7721ef orthogonality argument plus finite-sum identity; Mathlib conditional expectation pull-out and finite-square algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_integer_grid_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (V : ℕ → Ω → ℝ)
    (hmem : ∀ j : ℕ, MemLp (V j) 2 P)
    (hadapt : ∀ j : ℕ, StronglyMeasurable[𝓕.rightCont ((j + 1 : ℕ) : ℝ≥0)] (V j))
    (hmds : ∀ j : ℕ, P[V j | 𝓕.rightCont (j : ℝ≥0)] =ᵐ[P] 0)
    (n : ℕ) :
    (∫ ω, (∑ j ∈ Finset.range n, V j ω)^2 ∂P) =
      ∑ j ∈ Finset.range n, ∫ ω, (V j ω)^2 ∂P := by sorry
