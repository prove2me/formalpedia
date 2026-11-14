-- Prove2me | Theorems.Thm_APFPaper5_K3_turn_is_combination
-- name    : APFPaper5.K3.turn_is_combination
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:37:22.240694+00:00
-- url     : https://prove2.me/theorems/b0376949-aa0b-4afd-9abe-450ac889a077
-- title:
--   Every planar turn-form array is a real combination of identity and quarter turn
-- statement:
--   For arbitrary real a,b, turn a b equals add(smul a one)(smul b(turn 0 1)). This is an exact representation of the supplied array formula using identity and the quarter-turn array. No normalization is assumed. It does not identify a physical observable algebra, prove physical complex scalars, or establish centrality with respect to maps outside the displayed family. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1686-1717'}, {'locator': '1957'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_turns_are_complex_units.lean', 'line': 33, 'declaration': 'APFPaper5.K3.turn_is_combination', 'sha256': '98290b73a492a147b22a168ebf70cbd6a7ea55ab53bbd26157e655735e4c53d1'}]

import Definitions.Def_APFPaper5_K3_TwoMarkCost
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.turn_is_combination (a b : ℝ) : turn a b = add (smul a one) (smul b (turn 0 1)) := by sorry
