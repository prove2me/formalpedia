-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_iso_le_iSup
-- name    : Formalism.InvariantFactorPaths.PW.wl_iso_le_iSup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:35.124632+00:00
-- url     : https://prove2.me/theorems/a48c44d7-15da-4d8f-9614-277c9ede74c7
-- title:
--   PW: wl iso le i Sup
-- statement:
--   The PW construction uses the wl iso le i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L27-L30

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem Formalism.InvariantFactorPaths.PW.wl_iso_le_iSup (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) :
    IsoW G W la ≤ ⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)} := by sorry
