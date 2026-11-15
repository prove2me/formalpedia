-- Prove2me | Theorems.Thm_APFPaper5_K1_turnRound_on_two_is_the_quarter_turn
-- name    : APFPaper5.K1.turnRound_on_two_is_the_quarter_turn
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T02:44:59.119832+00:00
-- url     : https://prove2.me/theorems/b813a8e4-72f4-4cd6-8b37-6f875fd8cd34
-- title:
--   The supplied two-coordinate cyclic turn is a quarter turn
-- statement:
--   On Fin 2 records, the supplied turnRound 1 map equals quarterOn 1 0.
--
--   This is reference mathematics on Boolean records and the exact supplied predicates; it establishes no physical quantum reconstruction, admitted hold or additional foundation input.
-- source:
--   [{'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1276-1332;2168-2180', 'scope': 'Physical distinction descent and filter pull-back; does not itself supply NothingDrawn on the listed coordinate family.'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1680;1714-1723;2966-3076', 'scope': 'Conditional ledger isometry, connected real-carrier quarter turns, and remaining physical readout obligations.'}, {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json', 'revision': '2026-11-14.1', 'scope': 'B02 finite assignment amendment only; no installed hold or motion reading.'}, {'path': 'frozen/builder/RULING_hold_readings_2026-11-14.md', 'scope': 'Author discussion recorded as readings; explicit theorem hypotheses, not installed input adoption.'}, {'path': 'frozen/builder/TEE_UP_one_opposition_away_2026-11-14.md', 'scope': 'Advice/question only; no ruling selects every-state or occupant-state interpretation.'}, {'path': 'source/Theorems/Thm_APFPaper5_K1_no_half_of_a_quarter_turn.lean', 'sha256': 'b0ea29464b8eddf6ef08117da5c3a372f9fd8873af0516c1071c583215327724'}, {'path': 'source/Theorems/Thm_APFPaper5_K1_no_half_of_a_quarter_turn.lean', 'line': 68, 'declaration': 'APFPaper5.K1.turnRound_on_two_is_the_quarter_turn'}]

import Definitions.Def_APFPaper5_K1_Moves
import Definitions.Def_APFPaper5_K1_TurnRound
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1

theorem APFPaper5.K1.turnRound_on_two_is_the_quarter_turn :
    ∀ v : Fin 2 → Bool, turnRound 1 v = quarterOn 1 0 v := by sorry
