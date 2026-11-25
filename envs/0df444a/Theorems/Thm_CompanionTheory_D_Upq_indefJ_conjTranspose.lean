-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_indefJ_conjTranspose
-- name    : CompanionTheory.D.Upq.indefJ_conjTranspose
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:56.781713+00:00
-- url     : https://prove2.me/theorems/0923526f-3e54-40c1-8e1e-5affe3113eeb
-- title:
--   Upq: indef J conj Transpose
-- statement:
--   The Upq construction uses the indef J conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L397-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ContDiffOnExpPartialHomeomorphSymm.lean#L397-L399

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
open Matrix
open scoped Matrix.Norms.L2Operator
variable (p q : ℕ)

theorem CompanionTheory.D.Upq.indefJ_conjTranspose : (indefJ p q)ᴴ = indefJ p q := by sorry
