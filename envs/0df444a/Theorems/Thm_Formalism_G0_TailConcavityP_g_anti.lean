-- Prove2me | Theorems.Thm_Formalism_G0_TailConcavityP_g_anti
-- name    : Formalism.G0.TailConcavityP.g_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:26.215902+00:00
-- url     : https://prove2.me/theorems/c694e7be-acd5-4b5e-8b20-8cb5a917d7b4
-- title:
--   Tail Concavity P: g anti
-- statement:
--   The Tail Concavity P construction uses the g anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L67-L71

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.G0
open Formalism.G0.TailConcavityP

theorem Formalism.G0.TailConcavityP.g_anti (k : ℕ) {b b' : ℝ} (hb : 0 ≤ b) (h : b ≤ b') : g k b' ≤ g k b := by sorry
