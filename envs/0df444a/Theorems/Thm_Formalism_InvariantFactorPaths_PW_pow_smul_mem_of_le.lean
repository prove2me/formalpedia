-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_pow_smul_mem_of_le
-- name    : Formalism.InvariantFactorPaths.PW.pow_smul_mem_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:15.973433+00:00
-- url     : https://prove2.me/theorems/6160964f-6358-47a3-b0ea-859d5ebdf5bf
-- title:
--   PW: pow smul mem of le
-- statement:
--   The PW construction uses the pow smul mem of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/Discharge.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/Discharge.lean#L11-L19

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_Discharge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM

theorem Formalism.InvariantFactorPaths.PW.pow_smul_mem_of_le {p : ℕ} [Fact p.Prime] {σ : Type} (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    {k e : ℕ} (hke : k ≤ e) {y : MvPolynomial σ ℚ_[p]} (hy : ((p : ℚ_[p]) ^ k) • y ∈ L) :
    ((p : ℚ_[p]) ^ e) • y ∈ L := by sorry
