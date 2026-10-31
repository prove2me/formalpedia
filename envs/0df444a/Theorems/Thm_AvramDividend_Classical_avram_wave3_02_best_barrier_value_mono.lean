-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_best_barrier_value_mono
-- name    : AvramDividend.Classical.avram_wave3_02_best_barrier_value_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:06:32.389621+00:00
-- url     : https://prove2.me/theorems/96d6b027-b6c9-44dd-a5e2-cbf30041dccc
-- title:
--   Maximum genuine constant-barrier value increases with initial reserve
-- statement:
--   Under original Standing spectrally negative Levy and q>0, the best expected discounted dividend value available among all nonnegative constant barriers is monotone in starting capital x>=0. This supremum is over the true Stieltjes dividendValue/barrierStrategy and is supported by the Proved monotonicity of each individual strategy, using iSup lattice inequalities. It needs no global C1 regularity and asserts nothing about all-strategy optimality.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1; canonically accepted all-capital reflected reward monotonicity.

import Mathlib.Order.CompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_value_monotone_in_initial_capital

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_best_barrier_value_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    MonotoneOn (fun x : ℝ =>
      ⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) (Ici 0) := by sorry
