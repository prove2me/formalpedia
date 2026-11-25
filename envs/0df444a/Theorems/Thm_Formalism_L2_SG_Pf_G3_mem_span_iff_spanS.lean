-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_mem_span_iff_spanS
-- name    : Formalism.L2.SG.Pf.G3.mem_span_iff_spanS
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:33:32.443785+00:00
-- url     : https://prove2.me/theorems/1a0d8fdb-5c70-5fa2-bd0e-eea4dc747bd3
-- title:
--   G3: mem span iff span S
-- statement:
--   The G3 construction uses the mem span iff span S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L53-L60

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

theorem Formalism.L2.SG.Pf.G3.mem_span_iff_spanS {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ Submodule.span K (Set.range b) ↔ v ∈ spanS (⊤ : Subring K) b := by sorry
