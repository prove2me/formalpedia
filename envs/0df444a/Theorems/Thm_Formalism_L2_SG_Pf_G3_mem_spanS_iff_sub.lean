-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_mem_spanS_iff_sub
-- name    : Formalism.L2.SG.Pf.G3.mem_spanS_iff_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:33:53.330373+00:00
-- url     : https://prove2.me/theorems/262e2312-3cad-5eed-9bad-1a891e61ce03
-- title:
--   G3: mem span S iff sub
-- statement:
--   The G3 construction uses the mem span S iff sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L28-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L28-L51

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

theorem Formalism.L2.SG.Pf.G3.mem_spanS_iff_sub {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) {i₀ : ι} (h0 : h (b i₀) (b i₀) ≠ 0) (T : Subring K)
    (v : V) : (v ∈ spanS T b ∧ h (b i₀) v = 0) ↔
      v ∈ spanS T (fun j : {i // i ≠ i₀} => b j) := by sorry
