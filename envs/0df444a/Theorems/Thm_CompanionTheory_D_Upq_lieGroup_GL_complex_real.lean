-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_lieGroup_GL_complex_real
-- name    : CompanionTheory.D.Upq.lieGroup_GL_complex_real
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:41.468907+00:00
-- url     : https://prove2.me/theorems/ab4de2b7-6067-43fa-b3e2-38d6befc9025
-- title:
--   Upq: lie Group GL complex real
-- statement:
--   The Upq construction uses the lie Group GL complex real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L177-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L177-L178

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

theorem CompanionTheory.D.Upq.lieGroup_GL_complex_real (n : ℕ) (k : WithTop ℕ∞) :
    LieGroup 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) k (GL (Fin n) ℂ) := by sorry
