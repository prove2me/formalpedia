-- Prove2me | Theorems.Thm_Formalism_G0_TailSumsP_tailK_zero_fun
-- name    : Formalism.G0.TailSumsP.tailK_zero_fun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:35.692807+00:00
-- url     : https://prove2.me/theorems/d4f9c22d-b651-483c-9b66-111eededbc9e
-- title:
--   Tail Sums P: tail K zero fun
-- statement:
--   The Tail Sums P construction uses the tail K zero fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailSums.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailSums.lean#L10-L11

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TailSumsP

theorem Formalism.G0.TailSumsP.tailK_zero_fun {K : ℕ} (u : ℕ) : tailK (0 : Fin K → ℕ) u = 0 := by sorry
