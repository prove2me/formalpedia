-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain
-- name    : AvramDividend.Classical.dividendStrategy_plus_linear_drain
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:50:28.957477+00:00
-- url     : https://prove2.me/theorems/d14cd9e1-6b08-4ad3-84af-0f71aab006ac
-- title:
--   Adding a unit deterministic linear dividend rate preserves dividend strategy properties
-- statement:
--   For any nondecreasing, adapted, left-continuous cumulative dividend strategy D with D(0)=0, the control D_t+t is again a dividend strategy. Its additional linear component is deterministic and adapted, nondecreasing in t, continuous and zero initially. This closure principle is required to construct an admissible immediate-ruin witness for the initial-boundary audit of Proposition 4(i).
-- source:
--   Elementary properties of admissible cumulative dividend controls in Avram, Palmowski and Pistorius (2007), Section 2, combined with the Mathlib adapted-process closure under addition.

import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_plus_linear_drain
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    IsDividendStrategy 𝓕 (fun t ω => D t ω + (t : ℝ)) := by sorry
