-- Prove2me | Theorems.Thm_APFPaper5_K3_mix_has_no_reverse
-- name    : APFPaper5.K3.mix_has_no_reverse
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:47:36.737192+00:00
-- url     : https://prove2.me/theorems/f44f6b72-54c4-4a46-9e69-85b564f97663
-- title:
--   Mixing excludes a record-preserving intertwining reversal
-- statement:
--   For c*s nonzero, no map theta simultaneously preserves all plainNow records and intertwines mix c s with mix c (-s) in the stated order. This does not deny the algebraic inverse of a unit mixing map. The no-reverse results exclude a record-preserving intertwining map theta, not every inverse of mix. Rate coordinates and supplied descent are not original physical realization.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_reversal_on_the_carrier.lean', 'sha256': '3af3e90070062554c056d4828911dd4f3a8c15eb8a123a40a6ec247e749964e0', 'line': 201, 'declaration': 'APFPaper5.K3.mix_has_no_reverse'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1067'}]

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

theorem APFPaper5.K3.mix_has_no_reverse (c s : ℝ) (hcs : c * s ≠ 0) :
    ¬ ∃ theta : Held2 → Held2, (∀ h : Held2, plainNow (theta h) = plainNow h) ∧
      (∀ h : Held2, mix c s (theta h) = theta (mix c (-s) h)) := by sorry
