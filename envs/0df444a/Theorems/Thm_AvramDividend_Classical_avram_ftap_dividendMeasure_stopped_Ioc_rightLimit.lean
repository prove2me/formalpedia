-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_dividendMeasure_stopped_Ioc_rightLimit
-- name    : AvramDividend.Classical.avram_ftap_dividendMeasure_stopped_Ioc_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T11:11:49.828829+00:00
-- url     : https://prove2.me/theorems/331eec9f-8ee2-45b9-9562-d6ae383ea849
-- title:
--   Original dividend measure restricted to (0,τ] has stopped right-limit increments
-- statement:
--   For an original admissible-style left-continuous dividend strategy and any finite deterministic stop τ, the original Stieltjes dividend measure restricted to (0,τ] charges (a,b] by the difference between the right-continuous dividend representative at b∧τ and a∧τ. The actual Lean proof adapts the finite variation stopped signed Stieltjes case split of Mocho Go, FTAPTheorem42 Stochastic/FiniteVariation/FiniteVariationStoppedStieltjes.lean at commit 8c9c46e1b6e455f7d3069062957d4363879836ce, Apache-2.0, while applying the already Proved original Avram measure increment lemma. No assumptions are added to the original dividend strategy.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Stochastic/FiniteVariation/FiniteVariationStoppedStieltjes.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ftap_dividendMeasure_stopped_Ioc_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ a b : ℝ≥0) (hab : a ≤ b) :
    ((dividendMeasure D ω).restrict (Ioc (0 : ℝ) (τ : ℝ)))
      (Ioc (a : ℝ) (b : ℝ)) =
        ENNReal.ofReal (rightLimit D (min b τ) ω -
          rightLimit D (min a τ) ω) := by sorry
