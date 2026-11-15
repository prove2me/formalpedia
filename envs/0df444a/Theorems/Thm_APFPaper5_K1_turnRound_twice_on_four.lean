-- Prove2me | Theorems.Thm_APFPaper5_K1_turnRound_twice_on_four
-- name    : APFPaper5.K1.turnRound_twice_on_four
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:42:18.331638+00:00
-- url     : https://prove2.me/theorems/49dc236a-8962-4df7-82f7-0fdb68585192
-- title:
--   The supplied four-coordinate turn squares to two quarter turns
-- statement:
--   On Fin 4 records, turnRound 3 applied twice equals quarterOn 2 0 after quarterOn 3 1. Two simultaneous pair turns therefore have this supplied signed-permutation square root.
--
--   This is reference mathematics on Boolean records and the exact supplied predicates; it establishes no physical quantum reconstruction, admitted hold or additional foundation input.
-- source:
--   [{'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1276-1332;2168-2180', 'scope': 'Physical distinction descent and filter pull-back; does not itself supply NothingDrawn on the listed coordinate family.'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1680;1714-1723;2966-3076', 'scope': 'Conditional ledger isometry, connected real-carrier quarter turns, and remaining physical readout obligations.'}, {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json', 'revision': '2026-11-14.1', 'scope': 'B02 finite assignment amendment only; no installed hold or motion reading.'}, {'path': 'frozen/builder/RULING_hold_readings_2026-11-14.md', 'scope': 'Author discussion recorded as readings; explicit theorem hypotheses, not installed input adoption.'}, {'path': 'frozen/builder/TEE_UP_one_opposition_away_2026-11-14.md', 'scope': 'Advice/question only; no ruling selects every-state or occupant-state interpretation.'}, {'path': 'source/Theorems/Thm_APFPaper5_K1_no_half_of_a_quarter_turn.lean', 'sha256': 'b0ea29464b8eddf6ef08117da5c3a372f9fd8873af0516c1071c583215327724'}, {'path': 'source/Theorems/Thm_APFPaper5_K1_no_half_of_a_quarter_turn.lean', 'line': 72, 'declaration': 'APFPaper5.K1.turnRound_twice_on_four'}]

import Definitions.Def_APFPaper5_K1_Moves
import Definitions.Def_APFPaper5_K1_TurnRound
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1

theorem APFPaper5.K1.turnRound_twice_on_four :
    ∀ v : Fin 4 → Bool, turnRound 3 (turnRound 3 v) = quarterOn 2 0 (quarterOn 3 1 v) := by sorry
