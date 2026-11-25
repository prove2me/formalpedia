-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Cnt_last_unit_holds
-- name    : Formalism.L2.SG.Pf.Cnt.last_unit_holds
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:35:58.836926+00:00
-- url     : https://prove2.me/theorems/fe4c2113-40bf-53a8-8501-b94e5c4c6c11
-- title:
--   Cnt: last unit holds
-- statement:
--   The Cnt construction uses the last unit holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NormUnits.lean#L14-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NormUnits.lean#L14-L170

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DetUnitOfSelfdual
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LastRescaleOf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NormUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Cnt
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions
  Formalism.L2.SG.Pf.GluedFormOrthogonality Formalism.L2.SG.Pf.NormUnitsOrthogonality

theorem Formalism.L2.SG.Pf.Cnt.last_unit_holds : LastUnit := by sorry
