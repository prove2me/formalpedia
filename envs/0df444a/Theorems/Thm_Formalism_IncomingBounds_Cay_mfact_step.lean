-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_mfact_step
-- name    : Formalism.IncomingBounds.Cay.mfact_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:41.758137+00:00
-- url     : https://prove2.me/theorems/4e03924a-d9a2-45fd-b9d6-c78f30662dcc
-- title:
--   Cay: mfact step
-- statement:
--   The Cay construction uses the mfact step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L215-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L215-L235

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

theorem Formalism.IncomingBounds.Cay.mfact_step {σ : Type} (b : σ →₀ ℕ) (x : σ) (hx : 0 < b x) :
    mfact b = b x * mfact (b - Finsupp.single x 1) := by sorry
