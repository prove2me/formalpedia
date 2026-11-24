-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gram_majorant_bound
-- name    : Formalism.HermitianLatticeCounting.P.gram_majorant_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:34.615359+00:00
-- url     : https://prove2.me/theorems/d9671e07-9497-464c-907f-3e855bdfffde
-- title:
--   P: gram majorant bound
-- statement:
--   The P construction uses the gram majorant bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L792-L796
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L792-L796

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

theorem Formalism.HermitianLatticeCounting.P.gram_majorant_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.MajorantNormBound := by sorry
