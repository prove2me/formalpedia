-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_inf_pol_le
-- name    : Formalism.InvariantFactorPaths.PW.isoC_inf_pol_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:28.528378+00:00
-- url     : https://prove2.me/theorems/d8e95253-1f6b-4677-8424-3d1f204d65e8
-- title:
--   PW: iso C inf pol le
-- statement:
--   The PW construction uses the iso C inf pol le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/ZpClosedToAddSubgroup.lean#L28-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/ZpClosedToAddSubgroup.lean#L28-L46

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.PW.isoC_inf_pol_le (LL L2 : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    IsoC p LL j Cs la ⊓ Pol p r L2 ≤ IsoW (GAe p LL j (enumC Cs)) (Pol p r L2) (la ∘ enumC Cs) := by sorry
