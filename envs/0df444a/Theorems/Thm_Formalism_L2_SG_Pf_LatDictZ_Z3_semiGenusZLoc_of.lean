-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_semiGenusZLoc_of
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z3.semiGenusZLoc_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:58:04.818232+00:00
-- url     : https://prove2.me/theorems/3a75e723-149d-41dd-a40e-b6f851e43f0a
-- title:
--   Z3: semi Genus ZLoc of
-- statement:
--   The Z3 construction uses the semi Genus ZLoc of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L548-L577
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L548-L577

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0

theorem Formalism.L2.SG.Pf.LatDictZ.Z3.semiGenusZLoc_of (h1 : SemiGenusLoc) (h2 : PrimPlaneLoc) : SemiGenusZLoc := by sorry
