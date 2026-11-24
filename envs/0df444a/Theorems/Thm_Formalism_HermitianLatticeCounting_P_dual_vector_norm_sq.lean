-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_dual_vector_norm_sq
-- name    : Formalism.HermitianLatticeCounting.P.dual_vector_norm_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:58.629668+00:00
-- url     : https://prove2.me/theorems/6259a732-2eb4-4b2d-bcb0-33d32b796185
-- title:
--   P: dual vector norm sq
-- statement:
--   The P construction uses the dual vector norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L575-L647
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L575-L647

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
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
open scoped ComplexConjugate

theorem Formalism.HermitianLatticeCounting.P.dual_vector_norm_sq : Formalism.HermitianLatticeCounting.ExpansionTerms.DualVectorNormSq := by sorry
