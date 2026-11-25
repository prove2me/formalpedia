-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_mem_cutW_span_iff
-- name    : Formalism.L2.SG.Pf.G3.mem_cutW_span_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:42.777874+00:00
-- url     : https://prove2.me/theorems/033cae05-2c01-460a-9d36-a68aa9c0bba3
-- title:
--   G3: mem cut W span iff
-- statement:
--   The G3 construction uses the mem cut W span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L62-L68

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

theorem Formalism.L2.SG.Pf.G3.mem_cutW_span_iff {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) {i₀ : ι} (h0 : h (b i₀) (b i₀) ≠ 0) (v : V) :
    v ∈ cutW h (Submodule.span K (Set.range b)) (b i₀) ↔
      v ∈ Submodule.span K (Set.range (fun j : {i // i ≠ i₀} => b j)) := by sorry
