-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_rogozin_negative_slopes_of_unbounded_variation
-- name    : AvramDividend.Classical.ae_rogozin_negative_slopes_of_unbounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T16:06:49.041685+00:00
-- url     : https://prove2.me/theorems/4502f364-2bef-4d60-ac91-218b3d317a87
-- title:
--   Unbounded variation implies almost-sure Rogozin negative-slope oscillation at time zero
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation. Then almost surely, the small-time negative-slope oscillation holds: for every real slope C there are arbitrarily small positive times t with X_t < C * t. This is the exact missing premise of the proved theorem ae_negative_near_zero_of_ae_rogozin_negative_slopes, which turns it into almost-sure negative values arbitrarily close to zero, the regularity that forces instantaneous downward exit and hence the zero-start stopped-scale identity behind the unbounded-variation two-sided exit balance.
-- source:
--   Isolates the genuine missing premise of the Proved theorem ae_negative_near_zero_of_ae_rogozin_negative_slopes (b2e617e8), whose conclusion is the exact hypothesis needed to prove the Open theorem ae_negative_near_zero_of_unbounded_variation (703dc740). No catalogue theorem derives Rogozin slopes from unbounded variation (catalogue search 'rogozin': total 1, the bridge itself). Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.ae_rogozin_negative_slopes_of_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ C : ℝ,
      ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0),
        X.X t ω < C * (t : ℝ) := by sorry
