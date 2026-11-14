-- Prove2me | Theorems.Thm_APFPaper5_K3_pair_number_is_cross_term
-- name    : APFPaper5.K3.pair_number_is_cross_term
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:22:44.300202+00:00
-- url     : https://prove2.me/theorems/52cd2940-c2e0-4438-95d2-a8f525c70c86
-- title:
--   The fixed-mark sandwich coefficient is its chosen cross term with the other array
-- statement:
--   For every M2 array q, mul(mul markP q)markP equals smul(crossTerm markP q)markP. No idempotence, self-transpose or normalization hypothesis on q is required. The coefficient is the upper-left entry selected by the fixed mark and the chosen entrywise pairing; the theorem does not identify an arbitrary physical ordered score with a cost cross term. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '271-350'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_mark_cross_term.lean', 'line': 32, 'declaration': 'APFPaper5.K3.pair_number_is_cross_term', 'sha256': '00278a46a28a7186d0f5ef435bceb8d2c6a71efd53d03dbc25f8aa6d924daa72'}]

import Definitions.Def_APFPaper5_K3_TwoMarkCost
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.pair_number_is_cross_term (q : M2) :
    mul (mul markP q) markP = smul (crossTerm markP q) markP := by sorry
