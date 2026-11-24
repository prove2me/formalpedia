-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_map_mul_der
-- name    : Formalism.IncomingBounds.Cay.map_mul_der
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:37.572357+00:00
-- url     : https://prove2.me/theorems/6d157e94-f611-4a0a-a792-4b9f5a578ea0
-- title:
--   Cay: map mul der
-- statement:
--   The Cay construction uses the map mul der property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L49-L55

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

theorem Formalism.IncomingBounds.Cay.map_mul_der {n : Type*} [Fintype n] (X Y : Matrix n n A) :
    (X * Y).map D = X.map D * Y + X * Y.map D := by sorry
