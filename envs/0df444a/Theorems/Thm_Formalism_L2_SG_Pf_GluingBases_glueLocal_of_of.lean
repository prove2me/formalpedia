-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_glueLocal_of_of
-- name    : Formalism.L2.SG.Pf.GluingBases.glueLocal_of_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:19.75433+00:00
-- url     : https://prove2.me/theorems/916a17c5-7a50-4871-85be-f7bfaeb428e2
-- title:
--   Gluing Bases: glue Local of of
-- statement:
--   The Gluing Bases construction uses the glue Local of of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NondegOnOfCompl.lean#L63-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NondegOnOfCompl.lean#L63-L73

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsLatticeSpanO
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegOnOfCompl
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
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.L2.SG.Pf.GluingBases.glueLocal_of_of (hJ : JordanExists) (hV : GlueVecs) (hA : GlueAssemble) :
    Formalism.L2.SG.Pf.G7.GlueLocal := by sorry
