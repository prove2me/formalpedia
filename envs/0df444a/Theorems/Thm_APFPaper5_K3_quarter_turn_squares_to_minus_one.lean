-- Prove2me | Theorems.Thm_APFPaper5_K3_quarter_turn_squares_to_minus_one
-- name    : APFPaper5.K3.quarter_turn_squares_to_minus_one
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:23:49.598194+00:00
-- url     : https://prove2.me/theorems/d926d9f4-c82b-45e8-b781-241502ee7777
-- title:
--   The planar quarter-turn array squares to minus the identity
-- statement:
--   In the supplied real two-by-two array model, mul(turn 0 1)(turn 0 1)=smul(−1) one. The theorem is a matrix identity for the explicitly defined quarter-turn array. It does not establish that this array is a central physical scalar or that it is unseen by records; those assertions require different premises and an appropriate carrier. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1686-1717'}, {'locator': '1957'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_turns_are_complex_units.lean', 'line': 27, 'declaration': 'APFPaper5.K3.quarter_turn_squares_to_minus_one', 'sha256': '98290b73a492a147b22a168ebf70cbd6a7ea55ab53bbd26157e655735e4c53d1'}]

import Definitions.Def_APFPaper5_K3_TwoMarkCost
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.quarter_turn_squares_to_minus_one : mul (turn 0 1) (turn 0 1) = smul (-1) one := by sorry
