-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_rot2
-- name    : Formalism.L2.SG.Pf.G3.rot2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:17:06.268629+00:00
-- url     : https://prove2.me/theorems/f658583a-24eb-56cd-ad94-6db032b96254
-- title:
--   G3: rot2
-- statement:
--   The G3 construction uses the rot2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HermitianCoefficientIdentityOne.lean#L90-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/HermitianCoefficientIdentityOne.lean#L90-L252

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

theorem Formalism.L2.SG.Pf.G3.rot2 (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {ι : Type} [Fintype ι]
    [DecidableEq ι] {b : ι → V} {e : ι → ℕ} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hu : ∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) {i₀ j : ι} (hij : i₀ ≠ j)
    (hm : e i₀ ≤ e j) {α β : K} (hα : α ∈ S) (hβ : β ∈ S)
    (hY : IsUnitIn S (h (α • b i₀ + β • b j) (α • b i₀ + β • b j) * (π ^ e i₀)⁻¹)) :
    ∃ c : ι → V, (∀ p q, p ≠ q → h (c p) (c q) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ c i₀ = α • b i₀ + β • b j ∧
      (∀ k, k ≠ i₀ → k ≠ j → c k = b k) ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b := by sorry
