-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_expChart_GL_mem_maximalAtlas
-- name    : CompanionTheory.D.Upq.expChart_GL_mem_maximalAtlas
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:48.518206+00:00
-- url     : https://prove2.me/theorems/5b573495-b276-4049-b12a-12d6dbf3200a
-- title:
--   Upq: exp Chart GL mem maximal Atlas
-- statement:
--   The Upq construction uses the exp Chart GL mem maximal Atlas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L180-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L180-L183

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

theorem CompanionTheory.D.Upq.expChart_GL_mem_maximalAtlas (𝕂 : Type*) [RCLike 𝕂] (n : ℕ) (g : GL (Fin n) 𝕂)
    (k : WithTop ℕ∞) :
    expChartUnits 𝕂 g ∈ IsManifold.maximalAtlas 𝓘(𝕂, Matrix (Fin n) (Fin n) 𝕂) k (GL (Fin n) 𝕂) := by sorry
