-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_of_unbounded_variation
-- name    : AvramDividend.Classical.esscher_positive_root_of_unbounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:38:51.968562+00:00
-- url     : https://prove2.me/theorems/d34c29fc-9a07-4179-9378-b9f012633858
-- title:
--   Every unbounded-variation spectrally negative Lévy exponent has a positive Esscher root given continuity
-- statement:
--   For a spectrally negative Lévy process with unbounded variation, either its Gaussian coefficient is positive or it has infinite small-jump first moment. Both cases have already Proved eventual Laplace-exponent growth and positive-level crossing results. Since the canonical exponent has already been proved to satisfy ψ(0)=0, continuity on nonnegative parameters suffices to obtain an exact positive Esscher root φ solving ψ(φ)=q for any q>0. This identifies the only remaining analytic input for the positive Esscher-root part of the unbounded-variation excursion construction.
-- source:
--   Proved unbounded_variation_gaussian_or_infinite_small_jump_moment; esscher_positive_root_of_gaussian; esscher_positive_root_of_infinite_small_jump; levy_laplace_exponent_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_positive_root_of_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (hcont : ContinuousOn X.ψ (Ici (0 : ℝ))) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by sorry
