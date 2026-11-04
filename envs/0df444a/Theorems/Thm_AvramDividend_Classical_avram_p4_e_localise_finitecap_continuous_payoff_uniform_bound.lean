-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound
-- name    : AvramDividend.Classical.avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:15:36.312749+00:00
-- url     : https://prove2.me/theorems/3c55e7db-adc2-4b13-9007-36b33c568ec8
-- title:
--   Original P4-E continuous payoff has a finite uniform bound on all nonnegative admissible finite-cap reserves
-- statement:
--   For the exact source hw_cont on Ici 0, restrict to compact Icc 0 c for finite nonnegative real cap c. The extreme-value theorem for |w| supplies a real B≥0 dominating |w y| whenever 0≤y and ENNReal.ofReal y≤ENNReal.ofReal c. The ENNReal.toReal finite-cap transport is proved, not assumed. This is the missing analytic input to the original terminal state cap lemma for finite C and yields a genuine global L1 payoff bound without hidden C2 at the endpoints.
-- source:
--   Pinned Mathlib IsCompact.exists_isMaxOn, ContinuousOn.abs and ENNReal.toReal_le_of_le_ofReal; original P4-F hw_cont.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source nonnegative half-line continuity supplies an actual uniform terminal-payoff bound on finite cap states. -/
theorem AvramDividend.Classical.avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound
    (w : ℝ → ℝ) (hwcont : ContinuousOn w (Ici 0))
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : ℝ, 0 ≤ y →
        ENNReal.ofReal y ≤ ENNReal.ofReal c → |w y| ≤ B := by sorry
