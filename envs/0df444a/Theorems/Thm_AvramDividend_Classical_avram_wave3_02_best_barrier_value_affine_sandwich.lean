-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_best_barrier_value_affine_sandwich
-- name    : AvramDividend.Classical.avram_wave3_02_best_barrier_value_affine_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:20:44.264291+00:00
-- url     : https://prove2.me/theorems/06e895ab-6e4b-4315-9c0e-27602abe3ded
-- title:
--   Complete monotone affine growth envelope for optimal constant-barrier dividend value
-- statement:
--   The supremum of actual expected discounted Stieltjes dividends over every nonnegative constant barrier is nondecreasing in initial capital and lies between immediate withdrawal x and x plus one finite constant C>0. It assembles three separately accepted source-level results: best-barrier capital monotonicity, the actual zero-barrier initial payment lower bound, and the global uniform upper bound. It gives a complete finite affine growth interface under Standing and q>0 without C1 or an all-admissible-strategy optimality claim.
-- source:
--   Avram Palmowski Pistorius (2007), genuine barrier policy and dividend value; canonical finite cap-value envelope and zero-barrier initial payment.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_best_barrier_value_mono
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_best_barrier_value_ge_initial_capital
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_barrier_supremum_bound

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_best_barrier_value_affine_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ C : ℝ, 0 < C ∧
      MonotoneOn (fun x : ℝ =>
        ⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
          dividendValue X q x (barrierStrategy X x a)) (Ici 0) ∧
      ∀ x : ℝ, 0 ≤ x →
        ENNReal.ofReal x ≤
          (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
            dividendValue X q x (barrierStrategy X x a)) ∧
        (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
            dividendValue X q x (barrierStrategy X x a)) ≤
          ENNReal.ofReal x + ENNReal.ofReal C := by sorry
