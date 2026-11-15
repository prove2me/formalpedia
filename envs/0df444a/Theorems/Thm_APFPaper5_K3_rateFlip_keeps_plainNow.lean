-- Prove2me | Theorems.Thm_APFPaper5_K3_rateFlip_keeps_plainNow
-- name    : APFPaper5.K3.rateFlip_keeps_plainNow
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:49:38.680213+00:00
-- url     : https://prove2.me/theorems/c13c6b63-879a-4ea9-ab53-89a986707d7b
-- title:
--   Rate Flip keeps plain Now
-- statement:
--   Supporting result: rate Flip keeps plain Now. It holds for exactly the parameters and hypotheses displayed in the attached formal statement. Rate flip preserves present records but relative turns can reveal it. Rate-free present records determine states up to overall sign; specified record-preserving reversal conditions fail for nontrivial mixing. Descent of later-record predicates yields distinct classes for a supplied profile. The no-reverse results exclude a record-preserving intertwining map theta, not every inverse of mix. Rate coordinates and supplied descent are not original physical realization.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_reversal_on_the_carrier.lean', 'sha256': '3af3e90070062554c056d4828911dd4f3a8c15eb8a123a40a6ec247e749964e0', 'line': 50, 'declaration': 'APFPaper5.K3.rateFlip_keeps_plainNow'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1067'}]

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

theorem APFPaper5.K3.rateFlip_keeps_plainNow (h : Held2) : plainNow (rateFlip h) = plainNow h := by sorry
