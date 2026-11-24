-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_omega_step
-- name    : Formalism.IncomingBounds.Cay.omega_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:37.541327+00:00
-- url     : https://prove2.me/theorems/4163b46e-9f15-44cb-addf-de6046c6eb05
-- title:
--   Cay: omega step
-- statement:
--   The Cay construction uses the omega step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L369-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L369-L378

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

theorem Formalism.IncomingBounds.Cay.omega_step {n k : ℕ} (r c : Fin (k+2) → Fin n) (Q : MvPolynomial (PVar n) K) :
    diffOp ((Mg K n).submatrix r c).det Q =
      ∑ j : Fin (k+2), ((-1 : K) ^ (j : ℕ)) •
        pderiv (Sum.inl (r 0, c j)) (diffOp ((Mg K n).submatrix (r ∘ Fin.succ) (c ∘ j.succAbove)).det Q) := by sorry
