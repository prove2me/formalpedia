-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_noRel_image
-- name    : Formalism.FrobeniusOrbits.ThickExists.noRel_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:37.983414+00:00
-- url     : https://prove2.me/theorems/f625f3e8-8b25-4663-9de6-3a8c8c96df55
-- title:
--   Thick Exists: no Rel image
-- statement:
--   The Thick Exists construction uses the no Rel image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L85-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L85-L144

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.ThickExists

theorem Formalism.FrobeniusOrbits.ThickExists.noRel_image (L S d k : ℕ) (hL : 1 ≤ L) :
    NoRel ((Behrend.sphere S d k).image (Behrend.map (4 * L * d))) L := by sorry
