-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_spanS_le_of
-- name    : Formalism.L2.SG.Pf.G3.spanS_le_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:19:42.303105+00:00
-- url     : https://prove2.me/theorems/c91aefd8-1fd0-5c1a-8241-6c39d8952f9e
-- title:
--   G3: span S le of
-- statement:
--   The G3 construction uses the span S le of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HermitianCoefficientIdentityOne.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HermitianCoefficientIdentityOne.lean#L25-L29

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

theorem Formalism.L2.SG.Pf.G3.spanS_le_of {κ ι : Type} [Fintype κ] [Fintype ι] {f : κ → V} {g : ι → V}
    (hfg : ∀ k, f k ∈ spanS S g) {v : V} (hv : v ∈ spanS S f) : v ∈ spanS S g := by sorry
