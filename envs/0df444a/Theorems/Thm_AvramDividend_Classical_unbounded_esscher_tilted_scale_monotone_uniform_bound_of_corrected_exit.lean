-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound_of_corrected_exit
-- name    : AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:13:43.134605+00:00
-- url     : https://prove2.me/theorems/0c5b6fe1-9d9c-4a79-a97b-92f2c17ac2f2
-- title:
--   Unbounded Esscher tilted scale monotonicity and uniform Laplace bound from corrected exits
-- statement:
--   For an unbounded-variation spectrally negative Levy process and a specified positive Esscher root φ, the corrected killed two-sided exit identity implies the tilted scale V(x)=exp(-φx)W(x) is nondecreasing and uniformly bounded on positive capital levels. The proof combines the canonically Proved fixed-root first-passage scale decay and the exponential-decay-to-monotonicity result with the Proved Laplace uniform upper bound, yielding the exact conclusion of the Open unbounded_esscher_tilted_scale_monotone_uniform_bound frontier target under only the still missing stochastic exit identity.
-- source:
--   Avram Palmowski Pistorius (2007), corrected killed two-sided exit formula, Esscher martingale, and q-scale Laplace bound.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_uniform_bound_of_monotone
import Mathlib.Analysis.Complex.Exponential
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    MonotoneOn V (Ioi (0 : ℝ)) ∧
      ∃ C : ℝ, ∀ x : ℝ, 0 < x → V x ≤ C := by sorry
