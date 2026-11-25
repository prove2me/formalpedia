-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_mem_cutM_spanS_iff
-- name    : Formalism.L2.SG.Pf.G3.mem_cutM_spanS_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:10.842388+00:00
-- url     : https://prove2.me/theorems/48f5a8f6-a8b1-4f18-b21a-821e886d7143
-- title:
--   G3: mem cut M span S iff
-- statement:
--   The G3 construction uses the mem cut M span S iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L70-L74

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

theorem Formalism.L2.SG.Pf.G3.mem_cutM_spanS_iff {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) {i₀ : ι} (h0 : h (b i₀) (b i₀) ≠ 0) (v : V) :
    v ∈ cutM h (spanS S b) (b i₀) ↔ v ∈ spanS S (fun j : {i // i ≠ i₀} => b j) := by sorry
