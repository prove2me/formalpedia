-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_norm_pow_log_div_choose
-- name    : Formalism.InvariantFactorPaths.PW.norm_pow_log_div_choose
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:53.398933+00:00
-- url     : https://prove2.me/theorems/e4e53ddd-e102-4fdd-8602-2f61966895ed
-- title:
--   PW: norm pow log div choose
-- statement:
--   The PW construction uses the norm pow log div choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L78-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L78-L91

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

theorem Formalism.InvariantFactorPaths.PW.norm_pow_log_div_choose {n k N : ℕ} (hk : k ≤ n) (hn : n ≤ N) :
    ‖(p : ℚ_[p]) ^ (Nat.log p N) / (n.choose k : ℚ_[p])‖ ≤ 1 := by sorry
