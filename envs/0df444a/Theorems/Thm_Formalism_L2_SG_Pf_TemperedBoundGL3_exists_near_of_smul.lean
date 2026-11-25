-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_TemperedBoundGL3_exists_near_of_smul
-- name    : Formalism.L2.SG.Pf.TemperedBoundGL3.exists_near_of_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:39.651552+00:00
-- url     : https://prove2.me/theorems/cb0436ca-c6c6-5122-9519-3e64d13b8c87
-- title:
--   Tempered Bound GL3: exists near of smul
-- statement:
--   The Tempered Bound GL3 construction uses the exists near of smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsNearOfSmul.lean#L43-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsNearOfSmul.lean#L43-L69

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SplitAtOf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DivMemLocRingOfVFEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNearRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsNearOfSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.TemperedBoundGL3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA Formalism.HermitianLattices.Ext.L3.WCA Formalism.HermitianLattices.Ext.L3.Cell
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem Formalism.L2.SG.Pf.TemperedBoundGL3.exists_near_of_smul (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {n : 𝓞 F} (hn : n ≠ 0) {b : V}
    (hb : h b b = κ (ι n)) {s : 𝓞 F} (hs0 : s ≠ 0) (hsb : ι s • b ∈ A) :
    ∃ v : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ x, InL 𝔭 A 0 x → InI 𝔭 (v + k) (h x x - κ (ι n)) →
      ∃ y, InL 𝔭 A 0 y ∧ h y y = κ (ι n) ∧ InL 𝔭 A k (y - x) := by sorry
