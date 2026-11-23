-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_supp_sum_superset
-- name    : Formalism.IncomingBounds.Cay.supp_sum_superset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:37.954822+00:00
-- url     : https://prove2.me/theorems/7808bcc2-63a9-4b09-b784-9f900d8c1c3c
-- title:
--   Cay: supp sum superset
-- statement:
--   The Cay construction uses the supp sum superset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L136-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L136-L139

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
variable {σ M : Type} [AddCommMonoid M] (f : (σ →₀ ℕ) → K → M)

theorem Formalism.IncomingBounds.Cay.supp_sum_superset (h0 : ∀ a, f a 0 = 0) (p : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (hS : p.support ⊆ S) : ∑ a ∈ p.support, f a (coeff a p) = ∑ a ∈ S, f a (coeff a p) := by sorry
