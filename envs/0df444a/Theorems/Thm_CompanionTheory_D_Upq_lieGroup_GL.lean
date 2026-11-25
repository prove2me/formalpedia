-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_lieGroup_GL
-- name    : CompanionTheory.D.Upq.lieGroup_GL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:36.508823+00:00
-- url     : https://prove2.me/theorems/d889b170-5e0c-5ef8-8770-a7d2ac8a64db
-- title:
--   Upq: lie Group GL
-- statement:
--   The Upq construction uses the lie Group GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L174-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L174-L175

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
open scoped Matrix.Norms.L2Operator

theorem CompanionTheory.D.Upq.lieGroup_GL (𝕂 : Type*) [RCLike 𝕂] (n : ℕ) (k : WithTop ℕ∞) :
    LieGroup 𝓘(𝕂, Matrix (Fin n) (Fin n) 𝕂) k (GL (Fin n) 𝕂) := by sorry
