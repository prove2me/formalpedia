-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_positive_monotone_of_given_root
-- name    : AvramDividend.Classical.unbounded_tilted_positive_monotone_of_given_root
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T16:39:26.13677+00:00
-- url     : https://prove2.me/theorems/e0ec313a-5433-4ddd-a5c8-1fd20f1eab6c
-- title:
--   Fixed-root tilted scale monotonicity in unbounded variation
-- statement:
--   For a spectrally negative Levy process of unbounded variation with q-scale function W, if the Laplace exponent takes the value q at the given positive root phi, then the exponentially tilted scale function x |-> exp(-phi*x) * W(x) is monotone on the positive half-line. This isolates the exact fixed-root monotonicity missing from the exit-decay proof path: existing catalogue results only yield an existential root or require a corrected two-sided exit identity as premise.
-- source:
--   SPECIFIC_MISSING_LEMMA for AvramDividend.Classical.unbounded_esscher_root_exit_decay (0c9c7c97): the target supplies phi with Laplace root, and Proved tilted_monotone_implies_exit_decay (b5d3e4fd) reduces the decay conclusion to exactly this monotonicity. No catalogue theorem yields it for the given phi without a stopped-exit identity premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_tilted_positive_monotone_of_given_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Set.Ioi 0) := by sorry
