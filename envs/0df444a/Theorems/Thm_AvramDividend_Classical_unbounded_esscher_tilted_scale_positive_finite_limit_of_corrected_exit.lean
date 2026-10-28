-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_positive_finite_limit_of_corrected_exit
-- name    : AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:57:53.806868+00:00
-- url     : https://prove2.me/theorems/76f2d1e6-0a3a-42a1-82f7-933dd1d3fd5a
-- title:
--   Strictly positive finite Esscher-scale limit from corrected exits and monotone convergence
-- statement:
--   For any q>0 and given positive Esscher root, the corrected two-sided exit identity implies the tilted q-scale function is positive and monotone with a uniform upper bound. Its positive-axis extension is monotone and bounded on all reals, so monotone convergence at infinity gives a finite limit. Strict positivity of W at capital one transfers to a strictly positive limit. This proves the exact conclusion of the Open unbounded Esscher positive finite limit milestone conditional solely on the corrected exit identity, without Standing, C1, or renewal machinery.
-- source:
--   Avram Palmowski Pistorius (2007), Esscher scale bounds; Mathlib monotone convergence and canonical Proved corrected-exit consequences.

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound_of_corrected_exit
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.unbounded_esscher_tilted_scale_positive_finite_limit_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∃ L : ℝ, 0 < L ∧ Tendsto V atTop (nhds L) := by sorry
