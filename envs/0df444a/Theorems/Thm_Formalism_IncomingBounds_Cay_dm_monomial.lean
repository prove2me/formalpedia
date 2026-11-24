-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_dm_monomial
-- name    : Formalism.IncomingBounds.Cay.dm_monomial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:33.474059+00:00
-- url     : https://prove2.me/theorems/c60f7590-9dba-44c3-b42a-94ae636f0410
-- title:
--   Cay: dm monomial
-- statement:
--   The Cay construction uses the dm monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L188-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L188-L194

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

theorem Formalism.IncomingBounds.Cay.dm_monomial {σ : Type} (m a : σ →₀ ℕ) (c : K) :
    dm m (monomial a c) =
      if m ≤ a then monomial (a - m) (c * ((mfact a : K) / (mfact (a - m) : K))) else 0 := by sorry
