-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_sd_basis
-- name    : Formalism.L2.SG.Pf.G3.sd_basis
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:58:19.012474+00:00
-- url     : https://prove2.me/theorems/789d8af1-4820-54f6-bf80-6941bf0c10c2
-- title:
--   G3: sd basis
-- statement:
--   The G3 construction uses the sd basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SdBasisBot.lean#L41-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/SdBasisBot.lean#L41-L99

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

theorem Formalism.L2.SG.Pf.G3.sd_basis (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) : ∀ (n : ℕ) (W : Submodule K V) (M : AddSubgroup V),
    finrank K W ≤ n → IsSD S h W M →
    ∃ (k : ℕ) (f : Fin k → V), (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧
      (∀ i, IsUnitIn S (h (f i) (f i))) ∧ (∀ v, v ∈ spanS S f ↔ v ∈ M) ∧
      Submodule.span K (Set.range f) = W := by sorry
