-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_expChartUnits_symm_apply
-- name    : CompanionTheory.D.Upq.expChartUnits_symm_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:40.996065+00:00
-- url     : https://prove2.me/theorems/9bf050e9-cc23-40f3-baa9-e5df1bed0231
-- title:
--   Upq: exp Chart Units symm apply
-- statement:
--   The Upq construction uses the exp Chart Units symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L129-L130

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
variable (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
local notation "𝔢" => expPartialHomeomorph 𝕂 𝔸

theorem CompanionTheory.D.Upq.expChartUnits_symm_apply (g : 𝔸ˣ) (X : 𝔸) :
    (((expChartUnits 𝕂 g).symm X : 𝔸ˣ) : 𝔸) = g * exp X := by sorry
