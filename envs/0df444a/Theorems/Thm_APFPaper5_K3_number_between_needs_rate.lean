-- Prove2me | Theorems.Thm_APFPaper5_K3_number_between_needs_rate
-- name    : APFPaper5.K3.number_between_needs_rate
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:13:58.980193+00:00
-- url     : https://prove2.me/theorems/da33c497-97d2-424c-953c-ce600867a2d3
-- title:
--   Number between needs rate
-- statement:
--   If crossRe squared is strictly less than recA times recB for a Held2 state, crossIm is nonzero. These theorems conclude record non-inclusion, not economic elimination or physical B05 support novelty. Required records, hsound, availability of a smaller configuration and original A2 binding are not supplied here.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650,2221-2235'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_economy_instances.lean', 'sha256': '7e56a14b89897b37466d576ab71f614813db6c286f91ed745fc263f35b349fb9', 'line': 64, 'declaration': 'APFPaper5.K3.number_between_needs_rate'}]

import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation
import Theorems.Thm_APFPaper5_K3_firstOrder_of_two_directions
import Theorems.Thm_APFPaper5_K3_two_directions_needed
import Theorems.Thm_APFPaper5_K3_seen_common_turn_splits_an_object
import Theorems.Thm_APFPaper5_K4_two_sheets_separate_more
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
open APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]

theorem APFPaper5.K3.number_between_needs_rate (h : Held2) (hlt : crossRe h * crossRe h < recA h * recB h) :
    crossIm h ≠ 0 := by sorry
