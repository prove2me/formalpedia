-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_akCount_eq_skSet
-- name    : Formalism.L2.SG.Pf.discriminantNormShapes.akCount_eq_skSet
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:14:09.809841+00:00
-- url     : https://prove2.me/theorems/a5bf4980-7582-5ff6-90da-cfa0d1de2fb8
-- title:
--   discriminant Norm Shapes: ak Count eq sk Set
-- statement:
--   The discriminant Norm Shapes construction uses the ak Count eq sk Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscriminantNormShapes.lean#L78-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscriminantNormShapes.lean#L78-L107

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [Fact (IsFixF K F)]

theorem Formalism.L2.SG.Pf.discriminantNormShapes.akCount_eq_skSet {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b : Fin (finrank K (⊤ : Submodule K V)) → V}
    {a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F} (hb : IsJordanIn h ⊤ L 𝔭 b a) (k : ℕ) :
    akCount h L 𝔭 k = Nat.card (skSet K 𝔭 k a) := by sorry
