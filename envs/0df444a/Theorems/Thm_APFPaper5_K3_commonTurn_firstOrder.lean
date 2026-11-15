-- Prove2me | Theorems.Thm_APFPaper5_K3_commonTurn_firstOrder
-- name    : APFPaper5.K3.commonTurn_firstOrder
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:03:10.242225+00:00
-- url     : https://prove2.me/theorems/443ab80b-54de-46b0-be24-ab4e47da0b7a
-- title:
--   Common Turn first Order
-- statement:
--   For c squared plus s squared equal to one, the common turn applied twice to any Held2 state equals minus that state plus 2c times its first turn. This separates three readings of FirstOrder; it does not authorize extending a named K-layer hypothesis to all maps or joint systems.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_firstOrder_scope.lean', 'sha256': '418712b7511dcc97b2e861a33bb894f951f74832c67a3e441ca833fab820d181', 'line': 29, 'declaration': 'APFPaper5.K3.commonTurn_firstOrder'}]

import Definitions.Def_APFPaper5_K3_HeldMaps
import Theorems.Thm_APFPaper5_K3_commonTurn_unseen
import Theorems.Thm_APFPaper5_K3_records_are_cross_data
import Theorems.Thm_APFPaper5_K3_commonQuarter_commutes_common
import Theorems.Thm_APFPaper5_K3_same_records_give_common_turn
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.commonTurn_firstOrder (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    commonTurn c s (commonTurn c s h) =
      add2 (smul2 (-1) h) (smul2 (2 * c) (commonTurn c s h)) := by sorry
