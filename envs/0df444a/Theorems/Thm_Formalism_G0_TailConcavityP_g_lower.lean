-- Prove2me | Theorems.Thm_Formalism_G0_TailConcavityP_g_lower
-- name    : Formalism.G0.TailConcavityP.g_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:33.776592+00:00
-- url     : https://prove2.me/theorems/2aa2b8c1-eae1-4860-83ef-a2da37316a69
-- title:
--   Tail Concavity P: g lower
-- statement:
--   The Tail Concavity P construction uses the g lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailConcavity.lean#L86-L97

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

theorem Formalism.G0.TailConcavityP.g_lower {k : ℕ} {b : ℝ} (hk : (k : ℝ) ≤ b) (hb : 0 < b) : (k : ℝ) / (2 * b) ≤ g k b := by sorry
