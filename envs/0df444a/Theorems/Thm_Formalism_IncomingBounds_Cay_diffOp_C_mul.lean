-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_C_mul
-- name    : Formalism.IncomingBounds.Cay.diffOp_C_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:28.807658+00:00
-- url     : https://prove2.me/theorems/f712b3ea-cb02-4cb9-adf7-a8d7de35dabc
-- title:
--   Cay: diff Op C mul
-- statement:
--   The Cay construction uses the diff Op C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L293-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L293-L299

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

theorem Formalism.IncomingBounds.Cay.diffOp_C_mul {σ : Type} (c : K) (P Q : MvPolynomial σ K) :
    diffOp (MvPolynomial.C c * P) Q = c • diffOp P Q := by sorry
