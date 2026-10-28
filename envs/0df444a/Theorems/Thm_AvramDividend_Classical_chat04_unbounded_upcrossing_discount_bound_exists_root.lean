-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_upcrossing_discount_bound_exists_root
-- name    : AvramDividend.Classical.chat04_unbounded_upcrossing_discount_bound_exists_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:24:14.32496+00:00
-- url     : https://prove2.me/theorems/768bb8a6-23e5-413a-ab88-22a1ce2e7ae5
-- title:
--   Actual positive-root bound on unbounded-variation first-upcrossing discount
-- statement:
--   Every unbounded-variation spectrally negative Lévy process has a positive Esscher q-root. Choosing this root gives a quantitative upper bound on the Laplace transform of its strict first upper passage time, without assuming a root in the theorem statement. This supplies the first-passage estimate in the independent Wiener–Hopf resolvent route.
-- source:
--   Direct proof using Proved positive_esscher_root_of_unbounded_variation and levy_positive_root_unrestricted_upcrossing_discount_bound.

import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_unrestricted_upcrossing_discount_bound

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_upcrossing_discount_bound_exists_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (z : ℝ) (hz : 0 ≤ z) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      (∫⁻ ω, if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
        then ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTimeCorrected X z ω))))
        else 0 ∂P) ≤ ENNReal.ofReal (Real.exp (-(φ * z))) := by sorry
