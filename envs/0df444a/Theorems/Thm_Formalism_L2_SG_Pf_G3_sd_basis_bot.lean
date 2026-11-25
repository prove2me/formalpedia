-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_sd_basis_bot
-- name    : Formalism.L2.SG.Pf.G3.sd_basis_bot
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:30:25.860916+00:00
-- url     : https://prove2.me/theorems/d9e233b6-ad77-5180-9784-76e9298cea81
-- title:
--   G3: sd basis bot
-- statement:
--   The G3 construction uses the sd basis bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SdBasisBot.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SdBasisBot.lean#L16-L28

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanSSelf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SdBasisBot
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
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem Formalism.L2.SG.Pf.G3.sd_basis_bot {W : Submodule K V} {M : AddSubgroup V} (hM : IsSD S h W M) (hW : W = ⊥) :
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by sorry
