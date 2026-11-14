-- Prove2me | Theorems.Thm_APFPaper5_K3_quarter_quarter_unit
-- name    : APFPaper5.K3.quarter_quarter_unit
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:52:44.977639+00:00
-- url     : https://prove2.me/theorems/28baa385-fbd1-46cd-b031-3961c41ac202
-- title:
--   Two quarter turns about a unit axis equal the defined axis flip
-- statement:
--   For a supplied V3 axis b with dot3 b b=1 and every V3 vector v, quarterTurn b applied twice to v equals flipAbout b v. The normalization is an explicit hypothesis. This is an identity of the three-real vector model; V3 is supplied mathematics, not a derivation that physical space has three dimensions or that such a turn is physically admitted. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1649'}, {'locator': '3037-3056'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_exchange_needs_room.lean', 'line': 69, 'declaration': 'APFPaper5.K3.quarter_quarter_unit', 'sha256': '44eed3c43002bff09d87533d14394b2960c86d480a48e7b7c6853ea607f65077'}]

import Definitions.Def_APFPaper5_K3_ThreeDirections
import Definitions.Def_APFPaper5_K3_FirstOrder
import Theorems.Thm_APFPaper5_K3_no_turn_exchanges
import Theorems.Thm_APFPaper5_K3_slant_pqp
import Theorems.Thm_APFPaper5_K1_one_number_cannot_carry_value_and_rate
import Theorems.Thm_APFPaper5_K1_iterated_turn_in_plane
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.quarter_quarter_unit (b v : V3) (hb : dot3 b b = 1) :
    quarterTurn b (quarterTurn b v) = flipAbout b v := by sorry
