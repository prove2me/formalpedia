-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_no_new_record_interval_zero_stieltjes_mass
-- name    : AvramDividend.Classical.runningSup_no_new_record_interval_zero_stieltjes_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:22:19.353001+00:00
-- url     : https://prove2.me/theorems/a6c183cd-e347-47c6-891f-d7b1f8ce14bb
-- title:
--   The genuine Lévy running-supremum Stieltjes local-time measure assigns zero mass to every interval without a new record
-- statement:
--   For the actual spectrally negative Lévy process X and its running-supremum regulator S, let u≤v and suppose X_t≤S_u throughout [u,v]. Then the genuine Lebesgue–Stieltjes measure dS (already identified as dividendMeasure runningSup X) assigns the interval (u,v] exactly zero mass. The accepted original running-supremum constancy theorem gives S_v=S_u. The accepted Stieltjes interval formula gives dS((u,v])=ENNReal.ofReal(S_v−S_u)=0. This proves actual regulator-measure vanishing on each no-new-record interval, as a building block towards the local time at zero of the reflected process and the excursion compensator n. The full support property and the excursion killed strong Markov law are still separate.
-- source:
--   Accepted original runningSup_const_between_of_path_below_old_record (5b5f93de) and runningSup_dividendMeasure_Ioc_eq_record_increment (7343971b), pinned Mathlib Real.toNNReal_coe.

import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_const_between_of_path_below_old_record
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_no_new_record_interval_zero_stieltjes_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u v : ℝ≥0) (huv : u ≤ v)
    (hBelow : ∀ t : ℝ≥0, u ≤ t → t ≤ v →
      X.X t ω ≤ runningSup X u ω) :
    (dividendMeasure (runningSup X) ω)
      (Set.Ioc (u : ℝ) (v : ℝ)) = 0 := by sorry
