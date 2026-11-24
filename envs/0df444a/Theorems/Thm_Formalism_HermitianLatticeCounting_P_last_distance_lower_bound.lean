-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_last_distance_lower_bound
-- name    : Formalism.HermitianLatticeCounting.P.last_distance_lower_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:41.83403+00:00
-- url     : https://prove2.me/theorems/32ff4029-c772-49e8-bf19-1ea7382c3f7b
-- title:
--   P: last distance lower bound
-- statement:
--   The P construction uses the last distance lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L798-L847
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L798-L847

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset
open scoped ComplexConjugate

theorem Formalism.HermitianLatticeCounting.P.last_distance_lower_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.LastDistanceLowerBound := by sorry
