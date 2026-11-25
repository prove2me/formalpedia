-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_mem_span_of_spanS
-- name    : Formalism.L2.SG.Pf.G3.mem_span_of_spanS
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:32.801808+00:00
-- url     : https://prove2.me/theorems/a2398c08-5a1c-5cc3-bde5-a7ddbf4dcfa5
-- title:
--   G3: mem span of span S
-- statement:
--   The G3 construction uses the mem span of span S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HermitianCoefficientIdentityOne.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HermitianCoefficientIdentityOne.lean#L31-L35

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanSSelf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_HermitianCoefficientIdentityOne
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

theorem Formalism.L2.SG.Pf.G3.mem_span_of_spanS {ι : Type} [Fintype ι] {g : ι → V} {v : V} (hv : v ∈ spanS S g) :
    v ∈ Submodule.span K (Set.range g) := by sorry
