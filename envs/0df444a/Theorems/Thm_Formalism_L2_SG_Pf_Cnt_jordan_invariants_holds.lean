-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Cnt_jordan_invariants_holds
-- name    : Formalism.L2.SG.Pf.Cnt.jordan_invariants_holds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:32.232455+00:00
-- url     : https://prove2.me/theorems/9ecafbf3-114b-4d81-8337-1cd6fee6eb06
-- title:
--   Cnt: jordan invariants holds
-- statement:
--   The Cnt construction uses the jordan invariants holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/JordanInvariantsHolds.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/JordanInvariantsHolds.lean#L13-L21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscEquiv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanInvariantsHolds
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
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G2

theorem Formalism.L2.SG.Pf.Cnt.jordan_invariants_holds : JordanInv := by sorry
