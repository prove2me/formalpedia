-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G8_extU_mem
-- name    : Formalism.L2.SG.Pf.G8.extU_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:22:44.624818+00:00
-- url     : https://prove2.me/theorems/0ddfaca9-837b-4852-83b1-fb59b04029bb
-- title:
--   G8: ext U mem
-- statement:
--   The G8 construction uses the ext U mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/IsomFixOfExpOf.lean#L27-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/IsomFixOfExpOf.lean#L27-L57

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

theorem Formalism.L2.SG.Pf.G8.extU_mem {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) {g : orthK h U ≃ₗ[K] orthK h U} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (resF h (orthK h U))) :
    extU hUc g ∈ isomFix h U := by sorry
