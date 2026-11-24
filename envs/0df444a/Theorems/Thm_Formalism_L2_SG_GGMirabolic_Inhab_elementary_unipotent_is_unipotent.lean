-- Prove2me | Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_elementary_unipotent_is_unipotent
-- name    : Formalism.L2.SG.GGMirabolic.Inhab.elementary_unipotent_is_unipotent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:29.525442+00:00
-- url     : https://prove2.me/theorems/551f402b-4308-44f0-9937-05a8e980c49d
-- title:
--   Inhab: elementary unipotent is unipotent
-- statement:
--   The Inhab construction uses the elementary unipotent is unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L57-L60

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic Formalism.L2.SG.GGMirabolic.Inhab
open Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical

theorem Formalism.L2.SG.GGMirabolic.Inhab.elementary_unipotent_is_unipotent : IsUni 2 u12 := by sorry
