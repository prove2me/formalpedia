-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Cnt_glueLoc_of
-- name    : Formalism.L2.SG.Pf.Cnt.glueLoc_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:32.557741+00:00
-- url     : https://prove2.me/theorems/fb85922e-0c2c-4b60-a90c-4bdb014f7995
-- title:
--   Cnt: glue Loc of
-- statement:
--   The Cnt construction uses the glue Loc of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/BigLineBundleMoriwaki.lean#L48-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/BigLineBundleMoriwaki.lean#L48-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GmapEqSelfOfFix
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscIsoOfProj
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_BigLineBundleMoriwaki
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
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G6

theorem Formalism.L2.SG.Pf.Cnt.glueLoc_of (hi : ProjInto) (ho : ProjOnto) (hn : FibCount) : GlueLoc := by sorry
