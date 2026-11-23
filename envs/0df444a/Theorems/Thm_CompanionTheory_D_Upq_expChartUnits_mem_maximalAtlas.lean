-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_expChartUnits_mem_maximalAtlas
-- name    : CompanionTheory.D.Upq.expChartUnits_mem_maximalAtlas
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:52.556262+00:00
-- url     : https://prove2.me/theorems/c5ef1b83-83d2-46dd-a7d0-6867b355038a
-- title:
--   Upq: exp Chart Units mem maximal Atlas
-- statement:
--   The Upq construction uses the exp Chart Units mem maximal Atlas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L132-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L132-L166

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

theorem CompanionTheory.D.Upq.expChartUnits_mem_maximalAtlas (g : 𝔸ˣ) (n : WithTop ℕ∞) :
    expChartUnits 𝕂 g ∈ IsManifold.maximalAtlas 𝓘(𝕂, 𝔸) n 𝔸ˣ := by sorry
