-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_spanS_smul_mem
-- name    : Formalism.L2.SG.Pf.G3.spanS_smul_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:34.582074+00:00
-- url     : https://prove2.me/theorems/f7c2a2ac-f4cf-55a1-9804-da790cf1325f
-- title:
--   G3: span S smul mem
-- statement:
--   The G3 construction uses the span S smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L16-L20

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SplitAtOf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanIffSpanS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem Formalism.L2.SG.Pf.G3.spanS_smul_mem {ι : Type} [Fintype ι] {b : ι → V} {a : K} (ha : a ∈ S) {v : V}
    (hv : v ∈ spanS S b) : a • v ∈ spanS S b := by sorry
