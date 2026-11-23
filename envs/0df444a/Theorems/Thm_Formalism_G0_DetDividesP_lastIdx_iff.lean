-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_lastIdx_iff
-- name    : Formalism.G0.DetDividesP.lastIdx_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:57.867328+00:00
-- url     : https://prove2.me/theorems/947154be-aeb7-4575-b59c-15936a504252
-- title:
--   Det Divides P: last Idx iff
-- statement:
--   The Det Divides P construction uses the last Idx iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L12-L15

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
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
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {L : Type} [Field L] {r : ℕ}

theorem Formalism.G0.DetDividesP.lastIdx_iff (hr : 0 < r) (a : Fin r) : a.val + 1 = r ↔ a = ⟨r - 1, by omega⟩ := by sorry
