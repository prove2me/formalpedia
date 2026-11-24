-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_dadj
-- name    : Formalism.IncomingBounds.Cay.dadj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:43.602689+00:00
-- url     : https://prove2.me/theorems/e242e046-753a-4931-804b-1a638cd514a4
-- title:
--   Cay: dadj
-- statement:
--   The Cay construction uses the dadj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L351-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L351-L367

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

theorem Formalism.IncomingBounds.Cay.dadj {n : ℕ} (i j a b : Fin n) :
    (Mg K n).det * pderiv (Sum.inl (i, j)) (adjugate (Mg K n) a b) =
      adjugate (Mg K n) j i * adjugate (Mg K n) a b - adjugate (Mg K n) a i * adjugate (Mg K n) j b := by sorry
