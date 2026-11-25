-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Cnt_family_dual_holds
-- name    : Formalism.L2.SG.Pf.Cnt.family_dual_holds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:09.737095+00:00
-- url     : https://prove2.me/theorems/af2540c1-2398-5ffd-9501-08c5005ac22b
-- title:
--   Cnt: family dual holds
-- statement:
--   The Cnt construction uses the family dual holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DualFormInverse.lean#L14-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DualFormInverse.lean#L14-L154

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DualFLeOfInv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinearIndependentOrth
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DualFormInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Cnt
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions Formalism.L2.SG.Pf.GluedFormOrthogonality
  Formalism.L2.SG.Pf.DualFormInverse

theorem Formalism.L2.SG.Pf.Cnt.family_dual_holds : FamDual := by sorry
