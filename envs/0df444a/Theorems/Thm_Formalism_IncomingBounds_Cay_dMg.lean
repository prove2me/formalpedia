-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_dMg
-- name    : Formalism.IncomingBounds.Cay.dMg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:31.370797+00:00
-- url     : https://prove2.me/theorems/57e56089-9d3d-4e9a-bb4e-756f2cd680b5
-- title:
--   Cay: d Mg
-- statement:
--   The Cay construction uses the d Mg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L322-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L322-L333

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

theorem Formalism.IncomingBounds.Cay.dMg {n : ℕ} (i j p q : Fin n) :
    pderiv (Sum.inl (i, j)) (Mg K n p q) = if p = i ∧ q = j then 1 else 0 := by sorry
