-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Cnt_kernel_counting_holds
-- name    : Formalism.L2.SG.Pf.Cnt.kernel_counting_holds
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:58:58.697552+00:00
-- url     : https://prove2.me/theorems/aaf7b73e-e4c4-53a3-974e-c011249bf352
-- title:
--   Cnt: kernel counting holds
-- statement:
--   The Cnt construction uses the kernel counting holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscriminantGroupCounts.lean#L172-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscriminantGroupCounts.lean#L172-L174

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantGroupCounts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Cnt

theorem Formalism.L2.SG.Pf.Cnt.kernel_counting_holds : Formalism.L2.SG.Pf.G5.KerCount := by sorry
