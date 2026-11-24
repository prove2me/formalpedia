-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_Cay_der_prod
-- name    : Formalism.IncomingBounds.Cay.der_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:23.671905+00:00
-- url     : https://prove2.me/theorems/0358a0f2-be7a-45d7-a8e8-c2a1dd3f6ce9
-- title:
--   Cay: der prod
-- statement:
--   The Cay construction uses the der prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/Cayley.lean#L13-L27

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

theorem Formalism.IncomingBounds.Cay.der_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → A) :
    D (∏ j ∈ s, g j) = ∑ i ∈ s, D (g i) * ∏ j ∈ s.erase i, g j := by sorry
