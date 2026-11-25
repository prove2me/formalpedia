-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G8_gmap_extU
-- name    : Formalism.L2.SG.Pf.G8.gmap_extU
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:56.857671+00:00
-- url     : https://prove2.me/theorems/1d1b5aba-4940-5a08-b50f-275d1fca4ec2
-- title:
--   G8: gmap ext U
-- statement:
--   The G8 construction uses the gmap ext U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/IsomFixOfExpOf.lean#L59-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/IsomFixOfExpOf.lean#L59-L71

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

theorem Formalism.L2.SG.Pf.G8.gmap_extU {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) (X : Submodule (𝓞 K) W) :
    Formalism.HermitianLatticesTheory.gmap (extU hUc g) (X.map (incO W)) = (Formalism.HermitianLatticesTheory.gmap g X).map (incO W) := by sorry
