-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
-- name    : AvramDividend.Classical.levy_exponential_real_clock_extrema_drawdown_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:40:45.497986+00:00
-- url     : https://prove2.me/theorems/4390c2cb-aaa7-49a6-bafb-5492d3fc9555
-- title:
--   Genuine finite-time supremum, infimum and drawdown are jointly measurable at a real exponential clock
-- statement:
--   For any spectrally negative Lévy process X and a real clock coordinate u, the triple (sup_{s≤u+}X_s, −inf_{s≤u+}X_s, sup_{s≤u+}X_s−X_{u+}) is measurable as a function on the product of path space with the real clock line, where u+=max(u,0). This exact Borel statement ensures the Wiener–Hopf extrema and reflected drawdown are legal observables under an independent Exp(p) product probability.
-- source:
--   Composition of canonically Proved joint running-supremum measurability ecfe330c-0715-46eb-8469-74c57473ccf7, canonically Proved joint running-infimum theorem ae09696f-14ab-4f36-9a12-bc4042f0892e, and joint Lévy state measurability d55462c3-decf-40f0-9aff-439d356324d9, with pinned Mathlib measurable_real_toNNReal.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.levy_exponential_real_clock_extrema_drawdown_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : Ω × ℝ =>
      ((runningSup X z.2.toNNReal z.1,
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1}),
        runningSup X z.2.toNNReal z.1 -
          X.X z.2.toNNReal z.1)) := by sorry
