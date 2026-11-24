-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_X_mul
-- name    : Formalism.IncomingBounds.Cay.diffOp_X_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:13.272491+00:00
-- url     : https://prove2.me/theorems/69d888bd-c456-49d1-adb2-eaed9b957530
-- title:
--   Cay: diff Op X mul
-- statement:
--   The Cay construction uses the diff Op X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L284-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L284-L291

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

theorem Formalism.IncomingBounds.Cay.diffOp_X_mul {σ : Type} (x : σ) (P Q : MvPolynomial σ K) :
    diffOp (X x * P) Q = pderiv x (diffOp P Q) := by sorry
