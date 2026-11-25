-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_core_of_split
-- name    : Formalism.L2.SG.Pf.G3.core_of_split
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:44.374112+00:00
-- url     : https://prove2.me/theorems/3ea71e07-fc48-5acb-8d61-43e89725856d
-- title:
--   G3: core of split
-- statement:
--   The G3 construction uses the core of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanSSelf.lean#L104-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanSSelf.lean#L104-L170

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanIffSpanS
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanSSelf
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

theorem Formalism.L2.SG.Pf.G3.core_of_split (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hsp : SplitAt S π h) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ n →
    ∀ (b b' : ι → V) (e : ι → ℕ) (φ : V ≃ₗ[K] V),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i j, i ≠ j → h (b' i) (b' j) = 0) →
    (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, IsUnitIn S (h (b' i) (b' i) * (π ^ e i)⁻¹)) → φ ∈ Formalism.HermitianLatticesTheory.isom h →
    (∀ v, v ∈ Submodule.span K (Set.range b) ↔ φ v ∈ Submodule.span K (Set.range b')) →
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ Submodule.span K (Set.range b), h w v = 0) → g v = φ v) ∧
      ∀ v, v ∈ spanS S b ↔ g v ∈ spanS S b' := by sorry
