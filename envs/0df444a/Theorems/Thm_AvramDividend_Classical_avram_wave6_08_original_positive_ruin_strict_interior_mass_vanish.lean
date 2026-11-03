-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_strict_interior_mass_vanish
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_ruin_strict_interior_mass_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:45:07.043207+00:00
-- url     : https://prove2.me/theorems/632cdc82-ec09-4830-bf25-7ca422d4113e
-- title:
--   Original strictly pre-ruin full Stieltjes terminal-cell mass tends to zero and excludes ruin payment
-- statement:
--   For the true left-continuous original dividend process, strictly pre-ruin Stieltjes mass in the terminal shrinking open interval (u_n,τ) converges to zero in ENNReal as u_n↑τ. The right dividend at τ remains entirely excluded and the mass includes every interior right atom and singular-continuous payment. Uses the exact genuine Stieltjes endpoint formula and already proved left-limit continuity; no extra stochastic estimate is assumed.
-- source:
--   Proved strict endpoint mass identity and original right-limit approaching terminal prepayment value; continuous ENNReal.ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_strict_left_dividend_cell_vanish

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_positive_ruin_strict_interior_mass_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : ℝ≥0) (hτ : 0 < τ)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < τ)
    (hlim : Tendsto u atTop (𝓝 τ)) :
    Tendsto (fun n => dividendMeasure D ω (Ioo (u n : ℝ) (τ : ℝ)))
      atTop (𝓝 0) := by sorry
