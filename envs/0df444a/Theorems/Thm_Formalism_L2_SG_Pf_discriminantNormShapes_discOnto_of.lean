-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_discOnto_of
-- name    : Formalism.L2.SG.Pf.discriminantNormShapes.discOnto_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:30.245993+00:00
-- url     : https://prove2.me/theorems/37b9ec35-1dc2-5851-adcb-2e032de16516
-- title:
--   discriminant Norm Shapes: disc Onto of
-- statement:
--   The discriminant Norm Shapes construction uses the disc Onto of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscriminantNormShapes.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscriminantNormShapes.lean#L111-L117

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapes
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

theorem Formalism.L2.SG.Pf.discriminantNormShapes.discOnto_of (hU : UDModel) (hO : OrbitCount) : DiscOnto := by sorry
