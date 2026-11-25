-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_expChartUnits_self
-- name    : CompanionTheory.D.Upq.expChartUnits_self
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:15:41.361991+00:00
-- url     : https://prove2.me/theorems/17f93052-fcff-55bb-95ac-0ab74764781f
-- title:
--   Upq: exp Chart Units self
-- statement:
--   The Upq construction uses the exp Chart Units self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L125-L127

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

theorem CompanionTheory.D.Upq.expChartUnits_self (g : 𝔸ˣ) : expChartUnits 𝕂 g g = 0 := by sorry
