-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_hostThickExists
-- name    : Formalism.FrobeniusOrbits.hostThickExists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:51.612318+00:00
-- url     : https://prove2.me/theorems/5e6e5957-3f35-46e2-b5f9-69166ba81f40
-- title:
--   Frobenius Orbits: host Thick Exists
-- statement:
--   The Frobenius Orbits construction uses the host Thick Exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L181-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L181-L334

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
open Formalism Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000
open ThickExists

theorem Formalism.FrobeniusOrbits.hostThickExists : HostThickExists := by sorry
