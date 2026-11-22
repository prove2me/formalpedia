-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_kapC_mono
-- name    : Formalism.InvariantFactorPaths.PW.kapC_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:24.550806+00:00
-- url     : https://prove2.me/theorems/a9cead3d-f602-42eb-9eef-c7aa58260a66
-- title:
--   PW: kap C mono
-- statement:
--   The PW construction uses the kap C mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/Discharge.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/Discharge.lean#L7-L9

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

theorem Formalism.InvariantFactorPaths.PW.kapC_mono {p n n' d d' : ℕ} (hn : n ≤ n') (hd : d ≤ d') : kapC p n d ≤ kapC p n' d' := by sorry
