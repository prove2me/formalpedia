-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_sup_bound_of_truncated_integral
-- name    : Formalism.HermitianLatticeCounting.P.sup_bound_of_truncated_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:31.936054+00:00
-- url     : https://prove2.me/theorems/dab09987-3bef-4429-944a-c1f48aefc3b2
-- title:
--   P: sup bound of truncated integral
-- statement:
--   The P construction uses the sup bound of truncated integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L133-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L133-L133

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
open Formalism.HermitianLatticeCounting.ExpansionTerms MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

theorem Formalism.HermitianLatticeCounting.P.sup_bound_of_truncated_integral : Formalism.HermitianLatticeCounting.ExpansionTerms.LemSSupBound := by sorry
