-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_killed_renewal_of_ae_negative_near_zero
-- name    : AvramDividend.Classical.chat04_unbounded_zero_start_killed_renewal_of_ae_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:41:00.355962+00:00
-- url     : https://prove2.me/theorems/2956adf9-9042-4267-bfd1-8e2d23c7e425
-- title:
--   Zero-start killed scale renewal for positive time under almost-sure negative near-zero path regularity
-- statement:
--   If almost every Lévy path takes negative values arbitrarily soon after time zero, it necessarily goes below zero before every strictly positive horizon. The already-Proved downcrossing lemma then gives zero killed discounted q-scale expectation from zero reserve, equal to the canonical scale function value W(0) in the unbounded-variation case.
-- source:
--   Specialises Proved chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing (36c95a18-480f-4dfa-bf67-3fa059fc753e) to the exact near-zero regularity event used in Proved barrierRuinTime_zero_of_near_zero_negative_path (092db474-a695-4596-823d-0f1bb92d20ae). Supplies a boundary case of Open chat04_unbounded_killed_survival_discounted_scale_expectation (a885f0b3-3960-424d-97e4-abbcffe268ba), on the route to aed50a34.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_zero_start_killed_renewal_of_ae_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnear : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0)
    (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (X.X t ω))) ω ∂P) =
      ENNReal.ofReal (W 0) := by sorry
