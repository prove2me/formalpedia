-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_majorant_phase_estimate_holds
-- name    : Formalism.HermitianLatticeCounting.P.majorant_phase_estimate_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:38:00.00262+00:00
-- url     : https://prove2.me/theorems/3777487a-2c70-4991-adfe-852b0fccfc55
-- title:
--   P: majorant phase estimate holds
-- statement:
--   The P construction uses the majorant phase estimate holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L849-L863
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L849-L863

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

theorem Formalism.HermitianLatticeCounting.P.majorant_phase_estimate_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.MajorantPhaseChoice := by sorry
