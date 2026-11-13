-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_topcap_bad_uniform_cutoff_terminal_numeric_gap
-- name    : AvramDividend.Classical.avram_bvb22_topcap_bad_uniform_cutoff_terminal_numeric_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:53:43.356787+00:00
-- url     : https://prove2.me/theorems/2abadd00-6944-4775-abbb-a12908e67964
-- title:
--   Exact rational inequality certifying the top-cap stopped-terminal cutoff counterexample gap
-- statement:
--   For the original compound-Poisson counterexample candidate to the top-cap pathwise ledger child 28336ae5, the terminal reward at physical horizon one tenth strictly exceeds the initial value plus a rigorous envelope on its compensator truncated at one twentieth. This is the exact rational numerical gap in research/avram/bvc_topcap_uniform_source_counterexample_20261112.md. The lemma certifies only the scalar inequality. It is not an authoritative disproof of the stochastic theorem without the source model and event construction.
-- source:
--   The 12 November 2026 source-backed original compound Poisson no-jump counterexample calculation; pinned Mathlib Real.add_one_le_exp.

import Mathlib
open Classical Real
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_topcap_bad_uniform_cutoff_terminal_numeric_gap :
    (1 : ℝ) + (1 / 20) * (1 + (3 / 4) * (1 / 20)) <
      (47 / 40) * Real.exp (-(1 : ℝ) / 10) := by sorry
