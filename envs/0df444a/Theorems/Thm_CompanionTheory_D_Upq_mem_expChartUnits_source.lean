-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_mem_expChartUnits_source
-- name    : CompanionTheory.D.Upq.mem_expChartUnits_source
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:54.579672+00:00
-- url     : https://prove2.me/theorems/a835ef2f-da42-4c86-b882-0f3672efabfb
-- title:
--   Upq: mem exp Chart Units source
-- statement:
--   The Upq construction uses the mem exp Chart Units source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L121-L123

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

theorem CompanionTheory.D.Upq.mem_expChartUnits_source (g : 𝔸ˣ) : g ∈ (expChartUnits 𝕂 g).source := by sorry
