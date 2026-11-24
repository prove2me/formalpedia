-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_ddet
-- name    : Formalism.IncomingBounds.Cay.ddet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:06.751817+00:00
-- url     : https://prove2.me/theorems/c4827067-7a43-47dc-b33d-c3755764909d
-- title:
--   Cay: ddet
-- statement:
--   The Cay construction uses the ddet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L335-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L335-L349

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
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
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.IncomingBounds.Cay.ddet {n : ℕ} (i j : Fin n) :
    pderiv (Sum.inl (i, j)) (Mg K n).det = adjugate (Mg K n) j i := by sorry
