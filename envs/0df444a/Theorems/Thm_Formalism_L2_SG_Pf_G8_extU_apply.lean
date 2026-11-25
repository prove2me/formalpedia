-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G8_extU_apply
-- name    : Formalism.L2.SG.Pf.G8.extU_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:08:53.987849+00:00
-- url     : https://prove2.me/theorems/935d1e19-c4b7-57b8-b350-1c2300dc8165
-- title:
--   G8: ext U apply
-- statement:
--   The G8 construction uses the ext U apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/IsomFixOfExpOf.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/IsomFixOfExpOf.lean#L20-L25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IncOInjective
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsomFixOfExpOf
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G8
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.G8.extU_apply {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) (x : U) (y : W) :
    extU hUc g ((x : V) + y) = x + g y := by sorry
