-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_der_det
-- name    : Formalism.IncomingBounds.Cay.der_det
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:33.562022+00:00
-- url     : https://prove2.me/theorems/648ac970-5ca5-4c6b-aece-5412b4ecbb06
-- title:
--   Cay: der det
-- statement:
--   The Cay construction uses the der det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L29-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L29-L47

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

theorem Formalism.IncomingBounds.Cay.der_det {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n A) :
    D N.det = ∑ i, ∑ p, adjugate N i p * D (N p i) := by sorry
