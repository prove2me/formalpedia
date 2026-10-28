-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scaleDeriv_growth_of_stopped_balance
-- name    : AvramDividend.Classical.unbounded_scaleDeriv_growth_of_stopped_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:55:39.295227+00:00
-- url     : https://prove2.me/theorems/cfaf7320-aaa3-446b-a4e7-15bbf2b0547f
-- title:
--   Unbounded scale derivative growth from the exact stopped exit-scale balance
-- statement:
--   For an unbounded-variation spectrally negative Lévy process with positive discount, the exact stopped two-sided exit scale-balance identity and pointwise differentiability of the q-scale function on (0,∞) imply W'(x) tends to +∞. The existing Proved Esscher theorem extracts a positive root and monotone normalisation directly from stopped balance. The existing Proved deterministic growth theorem then gives coercivity. This is an independent route for the canonical finite cstar growth prerequisite if the native stopped balance is discharged before the corrected killed-exit identity.
-- source:
--   Avram Palmowski Pistorius (2007), two-sided exit identity (3.6) and scale function exponential growth; Proved Esscher stopped balance bridge.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_tilted_scale_mono_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scaleDeriv_growth_of_stopped_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hBalance : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    Tendsto (deriv W) atTop atTop := by sorry
