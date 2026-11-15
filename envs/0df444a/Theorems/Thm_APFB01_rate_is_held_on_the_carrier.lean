-- Prove2me | Theorems.Thm_APFB01_rate_is_held_on_the_carrier
-- name    : APFB01.rate_is_held_on_the_carrier
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:33:47.680027+00:00
-- url     : https://prove2.me/theorems/404837e2-186b-4f40-a094-6c0bd8b2262b
-- title:
--   Later-record descent separates model quotient classes
-- statement:
--   For s nonzero, if all equality predicates for the later plainNow record after relativeTurn c s descend through a supplied profile, there exists a state whose rate flip has the same present records but a distinct quotient class. The no-reverse results exclude a record-preserving intertwining map theta, not every inverse of mix. Rate coordinates and supplied descent are not original physical realization.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_reversal_on_the_carrier.lean', 'sha256': '3af3e90070062554c056d4828911dd4f3a8c15eb8a123a40a6ec247e749964e0', 'line': 214, 'declaration': 'APFB01.rate_is_held_on_the_carrier'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1067'}]

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

open APFPaper5.K3 in
theorem APFB01.rate_is_held_on_the_carrier {Process : Type uP} (profile : Held2 → Process → Prop)
    (c s : ℝ) (hs : s ≠ 0)
    (hfact : ∀ r : ℝ × ℝ × ℝ,
      APFB01.Descends profile (fun h => plainNow (relativeTurn c s h) = r)) :
    ∃ h : Held2, plainNow (rateFlip h) = plainNow h ∧
      APFB01.physicalClass profile (rateFlip h) ≠ APFB01.physicalClass profile h := by sorry
