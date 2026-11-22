-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_eq
-- name    : Formalism.IncomingBounds.Cay.diffOp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:48.35506+00:00
-- url     : https://prove2.me/theorems/db8e3f26-1c61-4e20-bca7-4c853e1c4884
-- title:
--   Cay: diff Op eq
-- statement:
--   The Cay construction uses the diff Op eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L171-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L171-L179

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

theorem Formalism.IncomingBounds.Cay.diffOp_eq {σ : Type} (P Q : MvPolynomial σ K) :
    diffOp P Q = ∑ m ∈ P.support, coeff m P • dm m Q := by sorry
