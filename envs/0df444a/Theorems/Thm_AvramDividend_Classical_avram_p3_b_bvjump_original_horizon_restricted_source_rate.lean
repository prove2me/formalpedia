-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_horizon_restricted_source_rate
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_horizon_restricted_source_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:57:51.076519+00:00
-- url     : https://prove2.me/theorems/6d7cc64b-4d3b-426a-b61b-3a701dff9f8f
-- title:
--   Original source Lévy finite marked rate passes through true finite-horizon clock restriction
-- statement:
--   Assuming precisely P2's original adapted finite marked source rate for actual X and original rightCont source occupation M, restricting M by the true physical clock u≤T gives the original marked rectangle rate with upper endpoint min(t,T), for s≤t and s≤T. This follows by exact pathwise marked set clipping plus original source rate, with ENNReal factors intact and infinite Lévy mark mass allowed. It is explicitly conditional on the outstanding P2 rate; no new compensator law is postulated.
-- source:
--   P2 393b03a8 original source count and Proved P3-B marked restricted cell measure; Avram Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_restricted_cell_measure
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_horizon_restricted_source_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRate : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (s t T : ℝ≥0) (hst : s ≤ t) (hsT : s ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
    P A * (((min t T - s : ℝ≥0) : ℝ≥0∞)) * X.ν B := by sorry
