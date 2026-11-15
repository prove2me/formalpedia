-- Prove2me | Theorems.Thm_APFPaper5_K3_relativeTurn_breaks_firstOrder_for_states
-- name    : APFPaper5.K3.relativeTurn_breaks_firstOrder_for_states
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:03:48.57008+00:00
-- url     : https://prove2.me/theorems/ad56633d-deab-4f69-8989-4655701b7e0e
-- title:
--   Relative Turn breaks first Order for states
-- statement:
--   For the explicit state (1,0,1,0), applying the relative quarter turn twice is not any real linear combination of that state and its first relative quarter turn. This separates three readings of FirstOrder; it does not authorize extending a named K-layer hypothesis to all maps or joint systems.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_firstOrder_scope.lean', 'sha256': '418712b7511dcc97b2e861a33bb894f951f74832c67a3e441ca833fab820d181', 'line': 51, 'declaration': 'APFPaper5.K3.relativeTurn_breaks_firstOrder_for_states'}]

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

theorem APFPaper5.K3.relativeTurn_breaks_firstOrder_for_states :
    ¬ ∃ α β : ℝ, relativeTurn 0 1 (relativeTurn 0 1 ⟨1, 0, 1, 0⟩) =
      add2 (smul2 α ⟨1, 0, 1, 0⟩) (smul2 β (relativeTurn 0 1 ⟨1, 0, 1, 0⟩)) := by sorry
