-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_lower_kill
-- name    : Formalism.InvariantFactorPaths.PW.lower_kill
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:53.931155+00:00
-- url     : https://prove2.me/theorems/3d1e445f-f4fc-4b58-a5b2-8b20e90342bf
-- title:
--   PW: lower kill
-- statement:
--   The PW construction uses the lower kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L331-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean#L331-L392

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}

theorem Formalism.InvariantFactorPaths.PW.lower_kill [CharZero K] (h : GlRel E) {NN : Submodule K W} (hN : ∀ a b, ∀ x ∈ NN, E a b x ∈ NN) {l : ℕ}
    (hev : ∀ (z : ι) (k : ℤ), ∀ x ∈ NN, E z z x = (k : K) • x → (l : ℤ) < |k| → x = 0)
    {z i : ι} (hiz : i ≠ z) {y : W} (hy : y ∈ NN) (he : E i z y = 0) (hii : E i i y = 0) (hzz : E z z y = 0) :
    E z i y = 0 := by sorry
