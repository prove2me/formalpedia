-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_Final_ExpansionTerms_majorant_lower_bound
-- name    : Formalism.HermitianLatticeCounting.Final.ExpansionTerms.majorant_lower_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:47.203227+00:00
-- url     : https://prove2.me/theorems/78eda34a-bed0-489e-b028-e96cd0161ab1
-- title:
--   Expansion Terms: majorant lower bound
-- statement:
--   The Expansion Terms construction uses the majorant lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/AlgebraicIdentityHigherDegree.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/AlgebraicIdentityHigherDegree.lean#L20-L20

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NormalisationIdentity
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.Final.ExpansionTerms.majorant_lower_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.LastDistanceLowerBound := by sorry
