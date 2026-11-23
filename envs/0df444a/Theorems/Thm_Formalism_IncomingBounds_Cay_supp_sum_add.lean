-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_supp_sum_add
-- name    : Formalism.IncomingBounds.Cay.supp_sum_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:32.387963+00:00
-- url     : https://prove2.me/theorems/f324eb7f-3f32-4308-a030-7d77af20c479
-- title:
--   Cay: supp sum add
-- statement:
--   The Cay construction uses the supp sum add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L141-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L141-L157

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

theorem Formalism.IncomingBounds.Cay.supp_sum_add (h0 : ∀ a, f a 0 = 0) (hadd : ∀ a x y, f a (x + y) = f a x + f a y)
    (p q : MvPolynomial σ K) :
    ∑ a ∈ (p + q).support, f a (coeff a (p + q)) =
      ∑ a ∈ p.support, f a (coeff a p) + ∑ a ∈ q.support, f a (coeff a q) := by sorry
