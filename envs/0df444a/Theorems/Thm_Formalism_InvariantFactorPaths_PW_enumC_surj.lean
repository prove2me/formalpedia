-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_enumC_surj
-- name    : Formalism.InvariantFactorPaths.PW.enumC_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:45.933095+00:00
-- url     : https://prove2.me/theorems/f43aa059-8aa2-4391-b04d-14ac9656063b
-- title:
--   PW: enum C surj
-- statement:
--   The PW construction uses the enum C surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L160-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L160-L163

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}

theorem Formalism.InvariantFactorPaths.PW.enumC_surj (Cs : Finset (Fin r)) {c : Fin r} (hc : c ∈ Cs) : ∃ a, enumC Cs a = c := by sorry
