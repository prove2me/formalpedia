-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gram_hilbert_schmidt_bound
-- name    : Formalism.HermitianLatticeCounting.P.gram_hilbert_schmidt_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:11.529935+00:00
-- url     : https://prove2.me/theorems/dec14666-b420-40f3-9c25-9e417a56f4ae
-- title:
--   P: gram hilbert schmidt bound
-- statement:
--   The P construction uses the gram hilbert schmidt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L865-L887
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L865-L887

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

theorem Formalism.HermitianLatticeCounting.P.gram_hilbert_schmidt_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.SkewOperatorFrobeniusBound := by sorry
