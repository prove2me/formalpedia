-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_terminal_payoff_of_no_early_hit
-- name    : AvramDividend.Classical.chat03_hittingBtwn_terminal_payoff_of_no_early_hit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:03:23.967142+00:00
-- url     : https://prove2.me/theorems/d585b3c9-ce8f-4b3f-861e-b2dbfcfa04fb
-- title:
--   Bounded hitting-time stopped clock equals a terminal horizon when every earlier sample avoids the hit set
-- statement:
--   For any discrete sampled process, a nonnegative physical mesh and a bounded hittingBtwn clock whose terminal grid point covers T, if every grid sample with physical time strictly before T avoids the hitting set, then the actual sampled stopping time capped at T is exactly T. Unlike no-exit-to-grid-end lemmas this permits hits at or after T, including the continuous exit time equalling T, and is suited to treating deterministic first-passage atoms.
-- source:
--   Pinned Mathlib hittingBtwn_le and hittingBtwn_mem_set_of_hittingBtwn_lt, together with NNReal monotonicity and the assumption of no pre-horizon hit. No stochastic martingale or regularity assumptions.

import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat03_hittingBtwn_terminal_payoff_of_no_early_hit
    {Ω β : Type*} (u : ℕ → Ω → β) (s : Set β) (ω : Ω)
    (mesh T : ℝ≥0) (m : ℕ)
    (hcap : T ≤ (m : ℝ≥0) * mesh)
    (hNoEarly : ∀ j : ℕ, (j : ℝ≥0) * mesh < T → u j ω ∉ s) :
    min (((hittingBtwn u s 0 m ω : ℕ) : ℝ≥0) * mesh) T = T := by
  sorry
