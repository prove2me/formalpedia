-- Prove2me | Theorems.Thm_Formalism_G0_TailConcavityP_g_four
-- name    : Formalism.G0.TailConcavityP.g_four
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:36.193348+00:00
-- url     : https://prove2.me/theorems/179a0d59-c1f1-4919-afa9-4031b16df27f
-- title:
--   Tail Concavity P: g four
-- statement:
--   The Tail Concavity P construction uses the g four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L73-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L73-L84

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

theorem Formalism.G0.TailConcavityP.g_four {k : ℕ} {b : ℝ} (hb : (k : ℝ) ≤ b) : g k (4 * b) ≤ g k b / 2 := by sorry
