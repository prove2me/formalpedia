-- Prove2me | Theorems.Thm_APFPaper1_Foundation_novelty_positive_gap_ledger
-- name    : APFPaper1.Foundation.novelty_positive_gap_ledger
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-10-11T19:54:41.697653+00:00
-- url     : https://prove2.me/theorems/7c06bdc2-7f96-44c3-a1fe-15edc710cfa3
-- title:
--   Support novelty gives a strict joint-cost increase
-- statement:
--   For the same supplied original-domain Ledger L, finite S and tested distinction d, if insert d S has a serving protocol and d is support-novel over S in the positive-window sense, then cost L S < cost L (insert d S). Joint feasibility and local novelty are hypotheses. This conditional infimum theorem does not assert universal novelty, attainment, a uniform family marginal floor or physical fidelity of arbitrary Ledger values.
-- source:
--   Paper 1 Supplement v9.27, lines 1754-1782 and 2615-2617. Exact recovered novelty_positive_gap proof reused with current provider binding and explicit Record carrier; original seed ID a76cedd2-9616-4767-8499-9b2625fc0c69. FOUNDATION_INPUTS revision 2026-10-04.1 unchanged.

import Definitions.Def_APFPaper1_SupportNovel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical
open APFPaper1.Foundation

theorem APFPaper1.Foundation.novelty_positive_gap_ledger {D P Record : Type*} [DecidableEq D] (L : Ledger D P Record)
    (S : Finset D) (d : D) (hf : Feasible L (insert d S))
    (hn : SupportNovel L S d) : cost L S < cost L (insert d S) := by
  sorry
