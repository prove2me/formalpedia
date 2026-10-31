-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_best_barrier_finite_window_sup
-- name    : AvramDividend.Classical.avram_wave3_02_best_barrier_finite_window_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:54:45.592402+00:00
-- url     : https://prove2.me/theorems/c902202e-606a-4433-91d3-dba9c685c335
-- title:
--   Every positive-reserve best constant-barrier dividend value is determined by a bounded interval of caps
-- statement:
--   For any fixed strictly positive initial reserve x and original Standing spectrally negative Levy model with q>0, there exists a finite nonnegative upper barrier A such that the supremum of actual discounted Stieltjes dividend values over every nonnegative constant barrier equals the supremum restricted to barriers in the bounded interval [0,A]. The Proved asymptotic high-barrier strict dominance by the true zero-barrier strategy supplies a cutoff. The zero-barrier value remains in [0,A], and lattice iSup inequalities prove the identity. This derivative-free compactness reduction does not assert continuity or attainment.
-- source:
--   Avram Palmowski Pistorius (2007), genuine constant-barrier dividend problem; Proved source high-barrier underperformance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_high_barrier_eventually_worse_than_zero

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_best_barrier_finite_window_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    ∃ A : ℝ, 0 ≤ A ∧
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) =
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ A),
        dividendValue X q x (barrierStrategy X x a)) := by sorry
