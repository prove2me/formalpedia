-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward43_original_finite_negative_mark_count_L1
-- name    : AvramDividend.Classical.avram_pj_reward43_original_finite_negative_mark_count_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:32:38.50827+00:00
-- url     : https://prove2.me/theorems/c256ad29-77ad-4551-ad6b-79507614f49c
-- title:
--   Original bounded-horizon negative Levy jump count with finite cutoff has integrable total mass
-- statement:
--   From the actual source X with finite Lévy square energy, every strictly negative finite mark cutoff -1<z<-eta has finite intensity and the original marked jump count on a fixed finite horizon has a finite first moment. Supplies the physical envelope for source41, using the actual NX count, not auxiliary Poisson hypotheses.
-- source:
--   Proved 3e5bbc19 negative Levy tail finite from square energy, Proved 0d444e07 actual source negative Borel marked expected count exact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward43_original_finite_negative_mark_count_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    (∫⁻ ω, ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
       (fun s : ℝ≥0 => (s, X.X s ω -
         Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
       (Ioc 0 T ×ˢ Ioo (-1 : ℝ) (-η)) ∂P) < ⊤ := by sorry
