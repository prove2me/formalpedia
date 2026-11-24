-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_norm_pow_p_le_one
-- name    : Formalism.InvariantFactorPaths.PW.norm_pow_p_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:13.054401+00:00
-- url     : https://prove2.me/theorems/be266afa-e682-4cfe-b348-23b83e3ba483
-- title:
--   PW: norm pow p le one
-- statement:
--   The PW construction uses the norm pow p le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L74-L76

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
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
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.InvariantFactorPaths.PW.norm_pow_p_le_one (k : ℕ) : ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := by sorry
