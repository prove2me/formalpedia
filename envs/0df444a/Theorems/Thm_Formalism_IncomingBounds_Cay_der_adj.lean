-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_der_adj
-- name    : Formalism.IncomingBounds.Cay.der_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:46.698037+00:00
-- url     : https://prove2.me/theorems/04545b7f-ee24-418e-96ef-acc84ad55bdc
-- title:
--   Cay: der adj
-- statement:
--   The Cay construction uses the der adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L57-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L57-L79

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
open MvPolynomial Matrix
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A)

theorem Formalism.IncomingBounds.Cay.der_adj {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n A) (a b : n) :
    N.det * D (adjugate N a b) =
      D N.det * adjugate N a b - ∑ p, ∑ q, adjugate N a p * D (N p q) * adjugate N q b := by sorry
