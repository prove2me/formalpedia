-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_glueVecs_of
-- name    : Formalism.L2.SG.Pf.GluingBases.glueVecs_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:53.937032+00:00
-- url     : https://prove2.me/theorems/b0585443-200b-4931-9c41-a2cdefd42b62
-- title:
--   Gluing Bases: glue Vecs of
-- statement:
--   The Gluing Bases construction uses the glue Vecs of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/IsGlueDataPre.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/IsGlueDataPre.lean#L52-L56

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegOnOfCompl
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsGlueDataPre
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

theorem Formalism.L2.SG.Pf.GluingBases.glueVecs_of (h1 : GlueVecsPre) (h2 : LastRescale) : GlueVecs := by sorry
