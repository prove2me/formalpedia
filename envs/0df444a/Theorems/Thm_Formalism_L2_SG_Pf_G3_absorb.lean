-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_absorb
-- name    : Formalism.L2.SG.Pf.G3.absorb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:08.153601+00:00
-- url     : https://prove2.me/theorems/f147f7b9-729c-4a74-8c0d-5f5701da038f
-- title:
--   G3: absorb
-- statement:
--   The G3 construction uses the absorb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ImportsAlt.lean#L21-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ImportsAlt.lean#L21-L75

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_HermitianCoefficientIdentityOne
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ImportsAlt
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

theorem Formalism.L2.SG.Pf.G3.absorb (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {ι : Type} [Fintype ι]
    [DecidableEq ι] {e : ι → ℕ} {i₀ : ι} (x : ι → K) (hx : ∀ i, x i ∈ S) :
    ∀ T : Finset ι, i₀ ∉ T → (∀ j ∈ T, e i₀ < e j) → ∀ b : ι → V,
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ c i₀ = b i₀ + ∑ j ∈ T, x j • b j ∧
      (∀ k, k ≠ i₀ → k ∉ T → c k = b k) ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b := by sorry
