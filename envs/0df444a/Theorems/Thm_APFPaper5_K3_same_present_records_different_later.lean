-- Prove2me | Theorems.Thm_APFPaper5_K3_same_present_records_different_later
-- name    : APFPaper5.K3.same_present_records_different_later
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:02:13.056848+00:00
-- url     : https://prove2.me/theorems/178be33c-f95c-455c-881d-afaee3addb2d
-- title:
--   Same present records different later
-- statement:
--   For any relative-turn parameter s nonzero, there is a state whose rate flip has equal plainNow but unequal plainNow after that relative turn. The no-reverse results exclude a record-preserving intertwining map theta, not every inverse of mix. Rate coordinates and supplied descent are not original physical realization.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_reversal_on_the_carrier.lean', 'sha256': '3af3e90070062554c056d4828911dd4f3a8c15eb8a123a40a6ec247e749964e0', 'line': 72, 'declaration': 'APFPaper5.K3.same_present_records_different_later'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1067'}]

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

theorem APFPaper5.K3.same_present_records_different_later (c s : ℝ) (hs : s ≠ 0) :
    ∃ h : Held2, plainNow (rateFlip h) = plainNow h ∧
      plainNow (relativeTurn c s (rateFlip h)) ≠ plainNow (relativeTurn c s h) := by sorry
