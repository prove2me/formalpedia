-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatEx_splitDiff_holds
-- name    : Formalism.L2.SG.Pf.LatEx.splitDiff_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:29.72079+00:00
-- url     : https://prove2.me/theorems/730c042b-3a62-4e85-a3ba-aa6e8e1ba835
-- title:
--   Lat Ex: split Diff holds
-- statement:
--   The Lat Ex construction uses the split Diff holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsDiff.lean#L10-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsDiff.lean#L10-L35

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx

theorem Formalism.L2.SG.Pf.LatEx.splitDiff_holds : SplitDiff := by sorry
