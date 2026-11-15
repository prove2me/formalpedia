-- Prove2me | Theorems.Thm_APFPaper5_K3_rateFree_present_records_fix_state
-- name    : APFPaper5.K3.rateFree_present_records_fix_state
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:59:39.183615+00:00
-- url     : https://prove2.me/theorems/33d3f4ab-6972-4b93-acc9-87c7ee224c1e
-- title:
--   Rate Free present records fix state
-- statement:
--   Two RateFree states with equal plainNow are equal or differ by the overall sign neg2. The no-reverse results exclude a record-preserving intertwining map theta, not every inverse of mix. Rate coordinates and supplied descent are not original physical realization.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_reversal_on_the_carrier.lean', 'sha256': '3af3e90070062554c056d4828911dd4f3a8c15eb8a123a40a6ec247e749964e0', 'line': 87, 'declaration': 'APFPaper5.K3.rateFree_present_records_fix_state'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1067'}]

import Definitions.Def_APFPaper5_K3_PresentRecords
import Definitions.Def_APFPaper5_K3_HeldMaps
import Definitions.Def_APFPaper5_K3_LinearOnTwoComponents
import Definitions.Def_APFPaper5_K4_CompositeOnly
import Theorems.Thm_APFPaper5_K3_no_direction_if_present_records_fix_later
import Theorems.Thm_APFB01_distinct_objects_of_later_record
import Theorems.Thm_APFB01_rate_is_held_of_reversal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

universe uP

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
open APFPaper5.K4 (RateFree)

theorem APFPaper5.K3.rateFree_present_records_fix_state (h k : Held2) (hh : RateFree h) (hk : RateFree k)
    (e : plainNow k = plainNow h) : k = h ∨ k = neg2 h := by sorry
