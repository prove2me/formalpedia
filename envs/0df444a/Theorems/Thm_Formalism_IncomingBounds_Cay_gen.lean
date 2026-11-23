-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_gen
-- name    : Formalism.IncomingBounds.Cay.gen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:05.90184+00:00
-- url     : https://prove2.me/theorems/14d77bfc-1203-4ff6-b8bf-ba5e4f784a91
-- title:
--   Cay: gen
-- statement:
--   The Cay construction uses the gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L397-L470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L397-L470

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

theorem Formalism.IncomingBounds.Cay.gen (n s : ℕ) : ∀ (k : ℕ) (r c : Fin (k+1) → Fin n),
    (Mg K n).det ^ k * diffOp ((Mg K n).submatrix r c).det ((Mg K n).det ^ (s+1)) =
      MvPolynomial.C (∏ a ∈ Finset.range (k+1), ((s : K) + 1 + a)) *
        ((Mg K n).det ^ s * ((adjugate (Mg K n)).submatrix c r).det)
  := by sorry
