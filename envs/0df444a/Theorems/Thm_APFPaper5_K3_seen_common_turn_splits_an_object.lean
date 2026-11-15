-- Prove2me | Theorems.Thm_APFPaper5_K3_seen_common_turn_splits_an_object
-- name    : APFPaper5.K3.seen_common_turn_splits_an_object
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:43:07.686266+00:00
-- url     : https://prove2.me/theorems/59b4c563-0ab6-4f8b-8353-be716ac3232a
-- title:
--   Seen common turn splits an object
-- statement:
--   If a map fails CommonTurnUnseenAfter, there exist two states with equal plainAfterTurn profiles and unequal post-map profiles. FirstOrder means second iterate in a two-vector span, not equivalence to faithful differentiable first jets or a derivation from economy. The reverse implication and exact two-dimensional physical minimality are not certified.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650,2058-2090'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_firstOrder_economy.lean', 'sha256': '18c13508d187b79c5c4e62912fc2007b8a37738e601401e754d9db7bbe19fd59', 'line': 74, 'declaration': 'APFPaper5.K3.seen_common_turn_splits_an_object'}]

import Definitions.Def_APFPaper5_K3_FirstOrder
import Definitions.Def_APFPaper5_K1_OrderedScore
import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K3_records_of_plainAfterTurn_eq
import Theorems.Thm_APFPaper5_K3_plainAfterTurn_eq_iff_records
import Theorems.Thm_APFPaper5_K3_pair_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_of_anticommutes
import Theorems.Thm_APFPaper5_K3_unseen_iff
import Theorems.Thm_APFPaper5_K3_square_commutes_quarter
import Theorems.Thm_APFPaper5_K3_unseen_of_fixed_by_records
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
open APFPaper5.K1

theorem APFPaper5.K3.seen_common_turn_splits_an_object (T : Held2 → Held2) (hseen : ¬ CommonTurnUnseenAfter T) :
    ∃ x y : Held2, plainAfterTurn x = plainAfterTurn y ∧
      plainAfterTurn (T x) ≠ plainAfterTurn (T y) := by sorry
