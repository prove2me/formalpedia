-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_tendsto
-- name    : AvramDividend.Classical.avram_p3_2_original_controlled_left_prestate_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:29:54.560767+00:00
-- url     : https://prove2.me/theorems/015a831f-e659-4937-9499-e45d8ae5c374
-- title:
--   Original Lévy controlled postpayment source converges to exact predictable left prestate
-- statement:
--   For the actual original spectrally negative Lévy process X and any original admissible left-continuous dividend strategy D, the physical reserve path x+X_t-D_{t+} approaches its literal Function.leftLim prestate when time approaches a strictly positive jump time from the left. The exact source uses X.leftLim and the Proved identity lim_{s↑t}D_{s+}=D_t, allowing simultaneous original claim and dividend atoms without assuming jumps are disjoint, and without equality-in-law. This directly supplies one missing premise in the P3-2 finite tagged nonlinear jump convergence; selecting physical left-grid times remains separate.
-- source:
--   SpectrallyNegativeLevy.leftLim from the source definition, and Proved original postpayment-left-limit theorem f9c3a5c4-3a58-45b7-b6da-8734693b863d. Exact Mathlib leftLim_eq_of_tendsto name confirmed from the pinned 0df444a declaration index; its exact type remains to be compiler-verified.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_controlled_left_prestate_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) (𝓝[<] t)
      (𝓝 (Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t)) := by sorry
