-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_survivor_pre_rightpayment_terminal_left_tendsto_ae
-- name    : AvramDividend.Classical.avram_p3_2_original_discounted_survivor_pre_rightpayment_terminal_left_tendsto_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:50:55.564521+00:00
-- url     : https://prove2.me/theorems/052f45a6-b9d0-4e51-aa0c-653a86c1b1fe
-- title:
--   Original strictly surviving discounted pre-rightpayment terminal left limit
-- statement:
--   For the original spectrally negative Lévy X and admissible left-continuous dividend strategy D, on strict survival at any deterministic positive time the discounted value w of the postpayment reserve approaching from the left converges almost surely to the actual discounted pre-rightpayment terminal at that time; w is continuous on nonnegative states.
-- source:
--   Use accepted original fixed-time reserve left convergence, original admissible preruin reserve nonnegativity, the dividendStrategy bound D≤rightLimit D, continuity of w relative to Ici 0, and continuous time discount. No atom at the horizon is lost.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_surviving_pre_rightpayment_terminal_left_tendsto_ae
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_discounted_survivor_pre_rightpayment_terminal_left_tendsto_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (q : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun s : ℝ≥0 =>
        Real.exp (-(q * (s : ℝ))) *
          w (x + X.X s ω - rightLimit D s ω))
        (𝓝[<] t)
        (𝓝 (Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω))) := by sorry
