-- Prove2me | Theorems.Thm_APFPaper5_K3_rateFlip_preserves_plain_records
-- name    : APFPaper5.K3.rateFlip_preserves_plain_records
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:03:14.460423+00:00
-- url     : https://prove2.me/theorems/953853e2-9f60-4d90-b468-f2764f83f551
-- title:
--   Rate reversal preserves the three plain model records
-- statement:
--   For every Held2 state, rateFlip leaves recA, recB and recSum unchanged. The two second coordinates are negated together, which preserves these three chosen quadratic values. The claim does not include the quarter-turned recombination record or the full designated continuation profile.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1957'}, {'locator': '2001-2038'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_quarter_turn_commutes.lean', 'line': 122, 'declaration': 'APFPaper5.K3.rateFlip_preserves_plain_records', 'sha256': '57021aaef5be76f2f202f050063b757acfd67825da4017c90cfa00acb50027b8'}]

import Definitions.Def_APFPaper5_K3_LinearOnTwoComponents
import Theorems.Thm_APFPaper5_K3_commonTurn_unseen
import Theorems.Thm_APFPaper5_K3_records_are_cross_data
import Theorems.Thm_APFPaper5_K3_commonQuarter_commutes_common
import Theorems.Thm_APFPaper5_K3_same_records_give_common_turn
import Theorems.Thm_APFPaper5_K3_cross_invariant_under_commonTurn
import Theorems.Thm_APFPaper5_K3_relativeTurn_keeps_own_records
import Theorems.Thm_APFPaper5_K3_relativeTurn_rotates_cross
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.rateFlip_preserves_plain_records (h : Held2) :
    recA (rateFlip h) = recA h ∧ recB (rateFlip h) = recB h ∧ recSum (rateFlip h) = recSum h := by sorry
