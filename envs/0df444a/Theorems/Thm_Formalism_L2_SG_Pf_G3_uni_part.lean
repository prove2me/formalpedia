-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G3_uni_part
-- name    : Formalism.L2.SG.Pf.G3.uni_part
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:35:23.643793+00:00
-- url     : https://prove2.me/theorems/e0912816-51f2-4408-a8c1-a3b353131367
-- title:
--   G3: uni part
-- statement:
--   The G3 construction uses the uni part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/UniPart.lean#L122-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/UniPart.lean#L122-L290

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SdBasisBot
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_UniPart
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

theorem Formalism.L2.SG.Pf.G3.uni_part {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    {e : ι → ℕ} {i₀ : ι} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hu : ∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) (x : ι → K) (hx : ∀ i, x i ∈ S)
    (hX : IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹)) :
    ∃ c : ι → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧ (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
      c i₀ = ∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i ∧ (∀ k, e k ≠ e i₀ → c k = b k) ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b := by sorry
