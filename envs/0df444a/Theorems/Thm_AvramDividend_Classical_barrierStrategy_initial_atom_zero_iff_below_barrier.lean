-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_atom_zero_iff_below_barrier
-- name    : AvramDividend.Classical.barrierStrategy_initial_atom_zero_iff_below_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:33:53.421306+00:00
-- url     : https://prove2.me/theorems/49e1d867-eeb7-462a-b68f-831169db4c70
-- title:
--   The initial Stieltjes dividend atom vanishes exactly when starting capital is below the barrier
-- statement:
--   For a nonnegative initial reserve and nonnegative barrier, the cumulative dividend Stieltjes measure assigns zero mass to the initial time exactly when x≤a. The exact mass is the nonnegative positive part of x−a, and the mass vanishes precisely when that positive part is zero. This gives an elementary measure-theoretic characterization of the immediate dividend intervention and complements the sharp continuity-at-zero criterion.
-- source:
--   Deduction from Proved barrierStrategy_initial_dividendMeasure_atom_formula (f5167fe3-64d3-445d-bd85-947f84817b2e).

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_dividendMeasure_atom_formula
import Mathlib.Topology.Instances.ENNReal.Lemmas
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_initial_atom_zero_iff_below_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (ω : Ω) :
    dividendMeasure (barrierStrategy X x a) ω ({0} : Set ℝ) = 0 ↔
      x ≤ a := by sorry
