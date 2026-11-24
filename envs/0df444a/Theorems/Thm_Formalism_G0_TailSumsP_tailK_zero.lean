-- Prove2me | Theorems.Thm_Formalism_G0_TailSumsP_tailK_zero
-- name    : Formalism.G0.TailSumsP.tailK_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:38.227943+00:00
-- url     : https://prove2.me/theorems/87c9c0d8-3f45-4d44-9b8b-577b5b08d263
-- title:
--   Tail Sums P: tail K zero
-- statement:
--   The Tail Sums P construction uses the tail K zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailSums.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailSums.lean#L7-L8

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

theorem Formalism.G0.TailSumsP.tailK_zero {K : ℕ} (α : Fin K → ℕ) : tailK α 0 = ∑ l, α l := by sorry
