-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_eventual_gap_exists_of_driftpos_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_eventual_gap_exists_of_driftpos_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T05:44:53.411451+00:00
-- url     : https://prove2.me/theorems/e1e871f2-4962-41b8-82ce-468fc3a1e113
-- title:
--   Positive drift yields an eventual Laplace gap index
-- statement:
--   Given strictly positive drift and convergence of the compensated small-jump integrals J to A, there exists an index N where the J-gap, q-gap and B-gap inequalities all hold simultaneously, with no Standing assumption. Helper D3a isolating gap existence in the drift-positive eventual-growth argument; feeds D3b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.p2m81_bv_eventual_gap_exists_of_driftpos_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ)
    (hdrift : 0 < X.drift)
    (hlim : Tendsto (fun n : ℕ => ∫ y : ℝ, (Real.exp (((n : ℝ) + 1) * y) - 1 - ((n : ℝ) + 1) * y) / ((n : ℝ) + 1) ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) atTop (nhds (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))) :
    ∃ N : ℕ, (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) - (((X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))) / 4) < (∫ y : ℝ, (Real.exp (((N : ℝ) + 1) * y) - 1 - ((N : ℝ) + 1) * y) / ((N : ℝ) + 1) ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))) ∧ q / ((N : ℝ) + 1) < (((X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))) / 4) ∧ (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν) / ((N : ℝ) + 1) < (((X.c + (∫ y : ℝ, |y| ∂(X.ν.restrict (Ioo (-1 : ℝ) 0))))) / 4) := by sorry
